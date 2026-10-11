## Worker report

Existing declaration delivery; no Lean module or proof is written. The definition is
`AlgebraicGeometry.Scheme.constantZMod` in
`WeilConjectures.AlgebraicGeometry.Sites.Kummer`, lines 379–384. I read its docstring,
complete body, namespace and ambient binders `(X : Scheme.{u}) (n : ℕ)` (line 134).
Its body is precisely
`(constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
  (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))`.
The record also lists the existing dependency theorem for the stalk clause; its module
is `Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk`, not the main record's module.

Source checked: I read the original blueprint markdown over read-only SSH on the
server at `literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-cd/
def-sc-constant-sheaves.md`, order 1007. It says exactly that F_n is the sheaf associated
to the constant presheaf Z/nZ and that its geometric stalks are Z/nZ. This agrees with
the item node. The local literature markdown is absent; the server copy was available.

Clause and hypothesis correspondence:

- Curve C: specialize `X` to `C : Scheme.{u}` over an algebraically closed field
  `k : Type u`, `[Field k] [IsAlgClosed k] [C.Over (Spec (.of k))]`, with
  `[AlgebraicGeometry.IsCurve (C ↘ Spec (.of k))]`. I read the recorded declaration
  in `WeilConjectures.AlgebraicGeometry.Curve`: IsCurve means separated, locally of
  finite type and quasi-compact over k, and topological Krull dimension at most one.
  The general existing construction applies to every such C; no stronger curve
  hypothesis is introduced and no specialization needs a new definition.
- Integer n ≥ 1: use `C.constantZMod n` for `n : ℕ` satisfying `1 ≤ n`.
  The existing construction works for every natural n, so restriction to the stated
  domain changes no value. It does not require primality or invertibility of n.
- Small étale site: `C.smallEtaleTopology`, sheaves valued in
  `AddCommGrpCat.{u + 1}`, exactly the abelian-sheaf category in the note of
  `def-weil-pbc-etale-sheaves` (module `Sheaf.AlgebraicGeometry.EtaleSheaves`).
  I opened that module; its set-valued local-constancy predicates are not needed here.
- Constant value Z/nZ: `AddCommGrpCat.of (ULift.{u + 1} (ZMod n))`.
  ULift raises only the universe and is canonically additively equivalent to ZMod n.
- Sheafification of the constant presheaf with identity restrictions:
  `CategoryTheory.constantSheaf` in `Mathlib.CategoryTheory.Sites.ConstantSheaf`,
  the mathlib_match of `def-weil-pbc-constant-sheaf`. I read its docstring and
  body `Functor.const Cᵒᵖ ⋙ presheafToSheaf J D`, which is exactly this construction.
- Geometric stalk Z/nZ: the recorded dependency
  `AlgebraicGeometry.Scheme.constantSheaf_geometricStalk_isIso` in
  `Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk`. I read its complete signature
  and proof docstring. Set `T := C`, `v := u`, and
  `E := AddCommGrpCat.of (ULift.{u + 1} (ZMod n))`. For every
  `Ω : Type u`, `[Field Ω] [IsAlgClosed Ω]` and `t : Spec (.of Ω) ⟶ C`, it states
  that the map from E through the sheafification unit at the identity neighbourhood
  to the stalk is an isomorphism. Its target sheaf is definitionally C.constantZMod n.
  Thus the canonical stalk has precisely the claimed group, after ULift's canonical
  identification. This clause is explicitly recorded, not dropped or reproved.

Edge cases checked: n = 1 gives the zero group and zero stalks; the empty curve is
allowed by IsCurve's dimension inequality and has no geometric points; disconnected
and zero-dimensional curves need no connectedness, smoothness or properness assumptions.
Integers divisible by the characteristic are included. n = 0 is outside the node's
range (the existing construction additionally makes sense there). Universe u is
arbitrary and the coefficient ULift places the finite group in the site universe.

Searches performed (raw service logs are in searches.jsonl):

- msearch LeanFinder, "constant etale sheaf with value ZMod n, sheafification of the
  constant presheaf on a curve": eight unrelated tilde/module-sheaf hits, no exact hit.
- msearch Loogle, "AlgebraicGeometry.Scheme.constantZMod, CategoryTheory.constantSheaf":
  unknown source identifier and no hits; Loogle indexes Mathlib, not the source library.
- msearch Loogle, "CategoryTheory.constantSheaf": twelve hits including the defining
  constantSheaf functor and its exact docstring.
- msearch grep, "constantZMod|noncomputable def constantSheaf", CategoryTheory:
  Mathlib ConstantSheaf.lean:66 and two adjunction declarations.
- msearch LeanSearch, "constant sheaf ZMod n on the small etale site": unavailable,
  Internal Server Error; no search verdict inferred from that failure.
- rg of the source AlgebraicGeometry/Sites for constantZMod: found the exact existing
  abbrev at Kummer.lean:382; the initial broader constant-sheaf search also found the
  module-valued `Etale.constantModSheaf`. I opened its docstring/body in
  `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs`: it gives Λ/dΛ in ModuleCat,
  so the exact abelian-group `constantZMod` is the appropriate declaration here.
- rg of `WeilConjectures` for def-sc-constant-sheaves: no blueprint-tag occurrence.
- rg of `lean/Sheaf` for constantZMod: no separate declaration; the existing
  ConstantSheafGeometricStalk module supplies the general stalk clause.
- rg of dag/lean_names_upstream.json for constantZMod and the item id: related Kummer
  maps and cohomology declarations, no exact item attachment. Direct source inspection
  establishes the existing abbrev despite its absence from that index.

No node fault, statement correction, disputed statement, new node or dependency module.
Only the item's lean field is changed. Under the existing-declaration rule no module
is compiled: the dry run checks the node/report delivery and existing declaration.
The independent second reader supplies the second-reading section.

## Second reading by J1

I independently read the node statement clause by clause against the recorded Lean declarations.

- **Curve object.** The node's curve (C) is the imported notion [def-sc-curves], whose
  declaration is `AlgebraicGeometry.IsCurve` in `WeilConjectures.AlgebraicGeometry.Curve`.
  The existing declaration `AlgebraicGeometry.Scheme.constantZMod` is polymorphic in an
  arbitrary `X : Scheme.{u}`, so specializing `X := C` imposes no extra geometric
  hypothesis. The source convention that the field is algebraically closed is carried by
  `IsCurve` and is not strengthened by the Lean definition.
- **Integer.** The node's (n\ge1) is rendered by the source binder `n : ℕ` in
  `constantZMod`; the node restricts its use to `1 ≤ n`. No primality, invertibility, or
  characteristic condition is added. The declaration also remains meaningful at `n = 0`,
  which does not weaken the node's stated domain.
- **Small étale site and coefficients.** `constantZMod` has type
  `Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}` and body
  `(constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
  (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))`. This is exactly the constant sheaf
  (sheafification of the constant presheaf with identity restrictions) with value
  `ℤ/nℤ`; `CategoryTheory.constantSheaf` is the recorded Mathlib dependency.
- **Geometric stalk clause.** The node cites
  [lem-weil-pbc-constant-sheaf-geometric-stalk]. Its declaration
  `AlgebraicGeometry.Scheme.constantSheaf_geometricStalk_isIso` states that the canonical
  map from the constant value through the sheafification unit to the geometric stalk is an
  isomorphism, for every algebraically closed geometric point. Instantiating its value by
  `AddCommGrpCat.of (ULift (ZMod n))` and `T := C` gives the node's stalk assertion; `ULift`
  only transports the coefficient to the site universe.

Edge cases were checked: `n = 1` gives the zero group and zero stalk; `n = 0` is outside
`n ≥ 1` but is supported by the existing definition; empty, disconnected, and
zero-dimensional curves are allowed by [def-sc-curves]; coefficients divisible by the
characteristic are included; and the universe parameter `u` is unrestricted. The empty
index-set issue is irrelevant because the construction has no index family.

For H4 I rechecked the source, Mathlib, and project declarations: `rg` finds the exact
`constantZMod` abbrev in `WeilConjectures/AlgebraicGeometry/Sites/Kummer.lean`; Mathlib
provides the underlying `CategoryTheory.constantSheaf`; and no competing `constantZMod`
declaration occurs in `lean/Sheaf`. Loogle/LeanFinder searches likewise found only the
same generic `constantSheaf` construction. The recorded stalk theorem is the sole project
dependency giving the geometric-stalk clause.

No mismatch was found. In particular, no new module, definition node, dependency module,
or statement correction is required; only the item's existing-declaration `lean` record is
delivered.
