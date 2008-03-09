@ECHO OFF
if "%1" == "goto" shift && goto continue

REM If they enter nothing, do all the benchmarks
set def=imaginary,spectral,real
if not "%1" == "" set def=%1
for %%i in (%def%) do for %%j in (yca\%%i\*.yca) do call %0 goto %%j
goto end

:continue
echo Processing %1
firstify %1 -himlv > %1.txt 2>&1

:end
