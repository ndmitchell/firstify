REM Build the entire nofib suite
REM Place all the result files in yca
REM Place all the object files in obj

if not exist yca mkdir yca
for %%i in (imaginary,spectral,real) do if not exist yca\%%i mkdir yca\%%i
for %%i in (imaginary,spectral,real) do for /d %%j in (%%i\*) do yhc %%j\Main --linkcore --hidir ..\..\obj\%%j --objdir ..\..\obj\%%j && copy obj\%%j\Main.yca yca\%%j.yca
