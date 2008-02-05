@echo off
if not "%1" == "" goto continue

if not exist imaginary\obj mkdir imaginary\obj
for %%i in (imaginary\*.yca) do call %0 %%~ni
goto end


:continue
echo Processing %1
main imaginary\%1.yca -mshl -o imaginary\obj\%1 > imaginary\obj\%1.txt 2>&1
goto end


:end
