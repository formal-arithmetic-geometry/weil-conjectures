# AlgebraicGeometry.topDegreeModuleAbelian

## Reason

The new proof compares the existing top-degree wrappers with native sheaves-of-modules
cohomology and derived functors. Repeated conversion between locally synthesized
wrapper dictionaries and native dictionaries makes the file exceed 60 seconds
(64--93 seconds in diagnostic compiles). Select the native category, additive and
abelian instances while elaborating the cached wrappers, then restore the normal
abelian priority and select the shared cached native abelian instance. Native category
and additive instances remain selected, avoiding conversions through their aliases. This is
an implementation repair: the mathematical objects, maps, formulas and signatures
are unchanged. The private `nativeModuleAbelian_eq` checks the instance equality by
`rfl`. No adopted source-library declaration changes.

## Old

The following original instance definitions and local reducibility selection are
preserved verbatim (the intervening source docstrings are omitted here):

```lean
local instance (priority := 2000) topDegreeModuleCategory (S : Scheme.{u}) :
    Category S.Modules :=
  SheafOfModules.instCategory (R := moduleRings S.toRingedSpace)

/-- The native additive structure, through the scheme-module alias.
Source: Mathlib sheaves of modules; Stacks, Tag 0096
(blueprint: lem-weil-pbc-top-degree-leray-square). -/
local instance (priority := 2000) topDegreeModulePreadditive (S : Scheme.{u}) :
    Preadditive S.Modules :=
  SheafOfModules.instPreadditive (moduleRings S.toRingedSpace)

/-- The native abelian structure, through the scheme-module alias.
Source: Mathlib sheaves of modules; Stacks, Tag 0096
(blueprint: lem-weil-pbc-top-degree-leray-square). -/
local instance (priority := 2000) topDegreeModuleAbelian (S : Scheme.{u}) :
    Abelian S.Modules :=
  inferInstanceAs (Abelian (SheafOfModules.{u} (moduleRings S.toRingedSpace)))

set_option allowUnsafeReducibility true in
attribute [local reducible] topDegreeModuleCategory topDegreeModulePreadditive
  topDegreeModuleAbelian

```

Previously there was no native instance-priority selection before these wrappers.

## New

Keep the old definitions and their reducibility attributes. Before their declarations, select:

```lean
attribute [local instance 3000] SheafOfModules.instCategory SheafOfModules.instPreadditive
  SheafOfModules.instAbelian
```

After their declarations, check:

```lean
private theorem nativeModuleAbelian_eq (S : Scheme.{u}) :
    topDegreeModuleAbelian S =
      (inferInstanceAs (Abelian (SheafOfModules.{u} (moduleRings S.toRingedSpace)))) := by
  rfl
```

Then restore the native abelian priority and select the same cached instance used by
the shared global construction; the native category and additive priorities remain 3000:

```lean
attribute [local instance 1000] SheafOfModules.instAbelian
attribute [local instance 4000] globalLerayModuleAbelian
```

The new global module constructs `globalLerayModuleAbelian` directly from the native
instance and uses it for its own shared constructions. Both presentations therefore
store the same instance term in their derived-category family and homology data.
The original top-degree wrapper remains available with its original body.

Existing public signatures, definition bodies and persistent attributes retain their
text. This local elaboration selection changes which definitionally equal instance
term is stored in implicit arguments, including those of the wrapper definitions.
The ring-sheaf alias is locally reducible. New proof code uses a whiskered natural transformation for single-image
naturality and respects transparency. The previous `false` settings
remain confined to the original definitions; they are reset to `true` for new proofs.

## Users

`tools/downstream.py --uses` over the existing public declarations identifies these
direct users. No current claim record was found for the four consumer modules.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.TopDegreeLeraySquare | G3 | Wrappers store native dictionaries directly; same mathematical definitions and theorem statement. |
| Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge | unclaimed | Uses the wrappers and square; its pasting proof additionally unfolds `globalLerayImage`, and its proof environment selects the shared native instances. |
| Sheaf.AlgebraicGeometry.UnitAffineComparisonTransportCore | unclaimed | Unfolds cohomology on the base; scalar restriction and underlying additive group unchanged. |
| Sheaf.AlgebraicGeometry.CurveAffineEdge | unclaimed | Unfolds the tensor base-change map; the same pinned composite is retained. Its existing local transparency setting also includes `globalLerayImage`. |
| Sheaf.AlgebraicGeometry.SmoothCurveEtaleStructureDirectImages | unclaimed | Unfolds derived images; the same derived functor and single object are retained. Two existing proof unfold lists now include `globalLerayImage`. |

The targets transitively use these definitions. Their denotations remain unchanged;
this elaboration repair is explicitly recorded for the independent definition/target
reader. All four direct consumer checks were accepted, with the adaptations recorded below
and in `top-degree-shared-leray-data.md`; the delivery tool performs the final
packet verification. Definition-meaning review remains open.

## Status

landed 20261026T065756-L-3232285 2026-10-26 (merge of deliver/G3/Sheaf.AlgebraicGeometry.TopDegreeLeraySquare)
