unit CllMethU;

// Please, don't delete this comment. \\
(*
  Copyright Owner: Yahe
  Copyright Year : 2007-2018

  Unit   : CllMethU.pas (platform independant)
  Version: 0.4a1

  Contact E-Mail: hello@yahe.sh
*)
// Please, don't delete this comment. \\

(*
  Description:

  Implements a rudimentary way of dynamically calling methods (e.g. from DLLs).
*)

(*
  Change Log:

  [Version 0.1a1] (09.05.2007: initial release)
  - CallMethod() (Cdecl-, Pascal-, Register- and Stdcall-Version) implemented
  - LoadMethod() implemented
  - UnloadMethod() implemented

  [Version 0.2a1] (11.05.2007: platform independant release)
  - LoadMethod() implemented platform independantly
  - UnloadMethod() implemented platform independantly

  [Version 0.2a2] (11.05.2007: bugfix release)
  - bugfixes in ASM-code -> registers loaded correctly now

  [Version 0.3a1] (11.05.2007: enhancement release)
  - "Safecall" added to supported call types
  - CallMethod() is now stdcall for security reasons

  [Version 0.4a1] (14.05.2007: record-support release)
  - records/structs are now supported as parameters
*)

(*
  Information: CallMethod()

  - native values are passed withouth special actions
  - native "const" values are passed withouth special actions
  - native "var" values are passed as a pointer to that value
  - native result values are returned in the EAX register

  - record values are passed as a pointer to that record
  - record "const" values are passed as a pointer to that record
  - record "var" values are passed as a pointer to that record
  - record result values are passed as an additional var parameter
  - record result values as safecall are passed as a pointer to that record as the result pointer

  - float values are passed as 3 seperate integer values pushed to the stack
  - float "const" values are passed as 3 seperate integer values pushed to the stack
  - float "var" values are passed as a pointer to that value
  - float result values are returned by the FPU: asm FSTP Result end;
*)

interface

uses
{$IFDEF MSWINDOWS}
  Windows;
{$ELSE MSWINDOWS}
  Libc;
{$ENDIF MSWINDOWS}

type
  TCallType = (ctCdecl, ctPascal, ctRegister, ctSafecall, ctStdcall);

{$IFDEF MSWINDOWS}
  TLibraryHandle = THandle;
{$ELSE MSWINDOWS}
  TLibraryHandle = Pointer;
{$ENDIF MSWINDOWS}

const
{$IFDEF MSWINDOWS}
  CEmptyLibraryHandle = 0;
{$ELSE MSWINDOWS}
  CEmptyLibraryHandle = nil;
{$ENDIF MSWINDOWS}

// CallMethod() is stdcall as it uses EAX, EBX, ECX and EDX registers extensively
function CallMethod(const ACallType : TCallType; const AMethodPointer : Pointer; const AParameters : array of LongWord; const AResultPointer : LongInt; const AUseResultPointer : Boolean; var ASafecallErrorCode : LongInt) : LongWord; stdcall;

function LoadMethod(const ALibraryName : String; const AMethodName : String; var ALibraryHandle : TLibraryHandle; var AMethodPointer : Pointer) : Boolean;
function UnloadMethod(var ALibraryHandle : TLibraryHandle; var AMethodPointer : Pointer; const AFreeLibrary : Boolean = true) : Boolean;

implementation

function CallMethod(const ACallType : TCallType; const AMethodPointer : Pointer; const AParameters : array of LongWord; const AResultPointer : LongInt; const AUseResultPointer : Boolean; var ASafecallErrorCode : LongInt) : LongWord; stdcall;
  type
    TLongWordArray = array of LongWord;
    TPosition      = (tpFirst, tpLast);

  function AddValue(const AParameters : array of LongWord; const AValue : LongWord; const APosition : TPosition) : TLongWordArray;
  var
    LIndex : LongInt;
  begin
    SetLength(Result, Succ(Length(AParameters)));
    for LIndex := Ord(APosition = tpFirst) to Pred(Length(AParameters) + Ord(APosition = tpFirst)) do
      Result[LIndex + Ord(APosition = tpFirst)] := AParameters[LIndex];

    if (APosition = tpFirst) then
      Result[0] := AValue
    else
      Result[High(Result)] := AValue;
  end;
var
  LEBP        : LongWord;
  LESP        : LongWord;
  LLength     : LongInt;
  LParameters : Pointer;
  LSize       : LongInt;
begin
  Result := High(Result);
  ASafecallErrorCode := 0;

  if AUseResultPointer then
  begin
    case ACallType of
      ctCdecl,
      ctStdcall :
      begin
        Result := CallMethod(ACallType, AMethodPointer, AddValue(AParameters, AResultPointer, tpFirst), 0, false, ASafecallErrorCode);
      end;

      ctPascal,
      ctRegister :
      begin
        Result := CallMethod(ACallType, AMethodPointer, AddValue(AParameters, AResultPointer, tpLast), 0, false, ASafecallErrorCode);
      end;

      ctSafecall :
      begin
        Result := CallMethod(ctStdcall, AMethodPointer, AddValue(AParameters, AResultPointer, tpLast), 0, false, ASafecallErrorCode);
      end;
    end;
  end
  else
  begin
    LLength     := Length(AParameters);
    LParameters := @AParameters;
    LSize       := SizeOf(LongWord);

    if (AMethodPointer <> nil) then
    begin
      case ACallType of
        ctCdecl,
        ctStdcall :
        begin
          asm
            PUSH EDI                                                              // save EDI-Register
            PUSH ESI                                                              // save ESI-Register

            PUSH EAX                                                              // save EAX-Register
            PUSH EBX                                                              // save EBX-Register
            PUSH ECX                                                              // save ECX-Register (Count-Register)
            PUSH EDX                                                              // save EDX-Register

            MOV  LEBP, EBP                                                        // save EBP-Register (Stack-Basepointer-Register)
            MOV  LESP, ESP                                                        // save ESP-Register (Stack-Register)

            XOR  EAX, EAX                                                         // empty EAX-Register
            MOV  EBX, LParameters                                                 // set EBX-Register
            MOV  ECX, LLength                                                     // set ECX-Register (Count-Register)

          @DoTest:
            TEST ECX, ECX                                                         // test ECX-Register (Count-Register)
            JZ   @DoCall                                                          // if zero jump to DoCall

            MOV  EAX, ECX                                                         // EAX = ECX
            DEC  EAX                                                              // EAX = ECX - 1
            MUL  EAX, LSize                                                       // EAX = (ECX - 1) * LSize
            ADD  EAX, EBX                                                         // EAX = (ECX - 1) * LSize + EBX
            PUSH [EAX]                                                            // push Parameter to Stack

            DEC  ECX                                                              // decrease ECX-Register (Count-Register)
            JMP  @DoTest                                                          // jump to DoTest

          @DoCall:
            CALL [AMethodPointer]                                                 // call Method
            MOV  Result, EAX                                                      // save Result

            MOV  EBP, LEBP                                                        // load EBP-Register (Stack-Basepointer-Register)
            MOV  ESP, LESP                                                        // load ESP-Register (Stack-Register)

            POP  EDX                                                              // load EDX-Register
            POP  ECX                                                              // load ECX-Register (Count-Register)
            POP  EBX                                                              // load EBX-Register
            POP  EAX                                                              // load EAX-Register

            POP  ESI                                                              // load ESI-Register
            POP  EDI                                                              // load EDI-Register
          end;
        end;

        ctPascal :
        begin
          asm
            PUSH EDI                                                              // save EDI-Register
            PUSH ESI                                                              // save ESI-Register

            PUSH EAX                                                              // save EAX-Register
            PUSH EBX                                                              // save EBX-Register
            PUSH ECX                                                              // save ECX-Register (Count-Register)
            PUSH EDX                                                              // save EDX-Register

            MOV  LEBP, EBP                                                        // save EBP-Register (Stack-Basepointer-Register)
            MOV  LESP, ESP                                                        // save ESP-Register (Stack-Register)

            XOR  EAX, EAX                                                         // empty EAX-Register
            MOV  EBX, LParameters                                                 // set EBX-Register
            MOV  ECX, LLength                                                     // set ECX-Register (Count-Register)

          @DoTest:
            TEST ECX, ECX                                                         // test ECX-Register (Count-Register)
            JZ   @DoCall                                                          // if zero jump to DoCall

            MOV  EAX, LLength                                                     // EAX = LLength
            SUB  EAX, ECX                                                         // EAX = LLength - ECX
            MUL  EAX, LSize                                                       // EAX = (LLength - ECX) * LSize
            ADD  EAX, EBX                                                         // EAX = (LLength - ECX) * LSize + EBX
            PUSH [EAX]                                                            // push Parameter to Stack

            DEC  ECX                                                              // decrease ECX-Register (Count-Register)
            JMP  @DoTest                                                          // jump to DoTest

          @DoCall:
            CALL [AMethodPointer]                                                 // call Method
            MOV  Result, EAX                                                      // save Result

            MOV  EBP, LEBP                                                        // load EBP-Register (Stack-Basepointer-Register)
            MOV  ESP, LESP                                                        // load ESP-Register (Stack-Register)

            POP  EDX                                                              // load EDX-Register
            POP  ECX                                                              // load ECX-Register (Count-Register)
            POP  EBX                                                              // load EBX-Register
            POP  EAX                                                              // load EAX-Register

            POP  ESI                                                              // load ESI-Register
            POP  EDI                                                              // load EDI-Register
          end;
        end;

        ctRegister :
        begin
          asm
            PUSH EDI                                                              // save EDI-Register
            PUSH ESI                                                              // save ESI-Register

            PUSH EAX                                                              // save EAX-Register
            PUSH EBX                                                              // save EBX-Register
            PUSH ECX                                                              // save ECX-Register (Count-Register)
            PUSH EDX                                                              // save EDX-Register

            MOV  LEBP, EBP                                                        // save EBP-Register (Stack-Basepointer-Register)
            MOV  LESP, ESP                                                        // save ESP-Register (Stack-Register)

            XOR  EAX, EAX                                                         // empty EAX-Register
            MOV  EBX, LParameters                                                 // set EBX-Register
            MOV  ECX, LLength                                                     // set ECX-Register (Count-Register)

          @DoTest:
            TEST ECX, ECX                                                         // test ECX-Register (Count-Register)
            JZ   @DoCall                                                          // if zero jump to DoCall

            CMP  ECX, 3                                                           // compare ECX-Register (Count-Register) to 3
            JLE  @DoCmp                                                           // if less or equal jump to DoCmp

            MOV  EAX, LLength                                                     // EAX = LLength
            SUB  EAX, ECX                                                         // EAX = LLength - ECX
            ADD  EAX, 3                                                           // EAX = LLength - ECX + 3
            MUL  EAX, LSize                                                       // EAX = (LLength - ECX + 3) * LSize
            ADD  EAX, EBX                                                         // EAX = (LLength - ECX + 3) * LSize + EBX
            PUSH [EAX]                                                            // push Parameter to Stack

            DEC  ECX                                                              // decrease ECX-Register (Count-Register)
            JMP  @DoTest                                                          // jump to DoTest

          @DoCmp:
            CMP  ECX, 1                                                           // compare ECX-Register (Count-Register) to 1
            JL   @DoCall                                                          // if less jump to DoCall

            MOV  EAX, 1                                                           // EAX = 1
            DEC  EAX                                                              // EAX = 1 - 1
            MUL  EAX, LSize                                                       // EAX = (1 - 1) * LSize
            ADD  EAX, EBX                                                         // EAX = (1 - 1) * LSize + EBX
            MOV  EAX, [EAX]                                                       // move first parameter to EAX

            CMP  ECX, 2                                                           // compare ECX-Register (Count-Register) to 2
            JL   @DoCall                                                          // if less jump to DoCall

            PUSH EAX                                                              // save EAX-Register
            MOV  EAX, 2                                                           // EAX = 2
            DEC  EAX                                                              // EAX = 2 - 1
            MUL  EAX, LSize                                                       // EAX = (2 - 1) * LSize
            ADD  EAX, EBX                                                         // EAX = (2 - 1) * LSize + EBX
            MOV  EDX, [EAX]                                                       // move second parameter to EDX
            POP  EAX                                                              // load EAX-Register

            CMP  ECX, 3                                                           // compare ECX-Register (Count-Register) to 3
            JL   @DoCall                                                          // if less jump to DoCall

            PUSH EAX                                                              // save EAX-Register
            PUSH EDX                                                              // save EDX-Register
            MOV  EAX, 3                                                           // EAX = 3
            DEC  EAX                                                              // EAX = 3 - 1
            MUL  EAX, LSize                                                       // EAX = (3 - 1) * LSize
            ADD  EAX, EBX                                                         // EAX = (3 - 1) * LSize + EBX
            MOV  ECX, [EAX]                                                       // move third parameter to ECX
            POP  EDX                                                              // load EDX-Register
            POP  EAX                                                              // load EAX-Register

          @DoCall:
            CALL [AMethodPointer]                                                 // call Method
            MOV  Result, EAX                                                      // save Result

            MOV  EBP, LEBP                                                        // load EBP-Register (Stack-Basepointer-Register)
            MOV  ESP, LESP                                                        // load ESP-Register (Stack-Register)

            POP  EDX                                                              // load EDX-Register
            POP  ECX                                                              // load ECX-Register (Count-Register)
            POP  EBX                                                              // load EBX-Register
            POP  EAX                                                              // load EAX-Register

            POP  ESI                                                              // load ESI-Register
            POP  EDI                                                              // load EDI-Register
          end;
        end;

        ctSafecall :
        begin
          ASafecallErrorCode := CallMethod(ctStdcall, AMethodPointer, AddValue(AParameters, LongWord(@Result), tpLast), AResultPointer, AUseResultPointer, ASafecallErrorCode);
        end;
      end;
    end;
  end;
end;

function LoadMethod(const ALibraryName : String; const AMethodName : String; var ALibraryHandle : TLibraryHandle; var AMethodPointer : Pointer) : Boolean;
begin
  Result := false;

  AMethodPointer := nil;
  if (ALibraryHandle = CEmptyLibraryHandle) then
{$IFDEF MSWINDOWS}
    ALibraryHandle := LoadLibrary(@ALibraryName[1]);
{$ELSE MSWINDOWS}
    ALibraryHandle := dlopen(@ALibraryName[1], RTLD_NOW);
{$ENDIF MSWINDOWS}
  if (ALibraryHandle <> CEmptyLibraryHandle) then
  begin
{$IFDEF MSWINDOWS}
    AMethodPointer := GetProcAddress(ALibraryHandle, @AMethodName[1]);
{$ELSE MSWINDOWS}
    AMethodPointer := dlsym(ALibraryHandle, @AMethodName[1]);
{$ENDIF MSWINDOWS}

    Result := (AMethodPointer <> nil);
  end;
end;

function UnloadMethod(var ALibraryHandle : TLibraryHandle; var AMethodPointer : Pointer; const AFreeLibrary : Boolean = true) : Boolean;
begin
  Result := false;

  if (ALibraryHandle <> CEmptyLibraryHandle) then
  begin
    AMethodPointer := nil;

    Result := not(AFreeLibrary);
    if not(Result) then
{$IFDEF MSWINDOWS}
      Result := FreeLibrary(ALibraryHandle);
{$ELSE MSWINDOWS}
      Result := (dlclose(ALibraryHandle) = 0);
{$ENDIF MSWINDOWS}
    if (Result and AFreeLibrary) then
      ALibraryHandle := CEmptyLibraryHandle;
  end;
end;

end.
