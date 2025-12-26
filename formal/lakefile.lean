import Lake
open Lake DSL

package PvNP where

lean_lib PvNP
lean_lib External
lean_lib Notes

require Paperproof from git "https://github.com/Paper-Proof/paperproof.git"@"main"/"lean"
