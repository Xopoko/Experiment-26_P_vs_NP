# External stubs (ASSUMPTION)

Placeholders for external theorems should be declared as explicit axioms in Lean,
with precise citations (authors, year, theorem number, page).

Template (in a Lean file):

```
namespace PvNP.External

-- ASSUMPTION: <authors, year, theorem, page>
axiom external_placeholder : True

end PvNP.External
```

Policy: the final theorem must not depend on any ASSUMPTION.
