# Track script and auto-run test on the script when modified.
# Usage: ./track.sh kappa|simple|degree <file>
if command -v entr
then
  echo scripts/$2 | entr ./test.native load $1 scripts/$2
else 
  echo "You need entr to use this script"
fi
