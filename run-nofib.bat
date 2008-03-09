@ECHO OFF

if not "%1" == "" goto continue
for %%i in (imaginary) do for %%j in (yca\%%i\*.yca) do call %0 %%j
goto end

:continue
echo Processing %1
firstify %1 -himlv > %1.txt 2>&1

:end
