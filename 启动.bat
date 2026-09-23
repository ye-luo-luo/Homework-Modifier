@echo off
cd /d "%~dp0"
where pythonw >nul 2>nul
if %errorlevel%==0 (
    start "" pythonw "%~dp0代码\启动.py"
) else (
    start "" python "%~dp0代码\启动.py"
)
