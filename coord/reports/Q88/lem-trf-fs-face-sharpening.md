## Worker report

The module `Sheaf.TraceFormula.FsFaceSharpening` states
`AlgebraicGeometry.fs_face_sharpening`, with its sole proof `sorry`. Five concrete helpers
present the subgroup, quotient and canonical maps already specified inline by the node.
No additional notion or independent theorem is introduced. No statement correction,
dependency repair or disputed statement is needed.

The Lean uses multiplicative notation throughout, matching the existing localization and
fs predicate. This is the node's additive convention transported by the usual type tag:
product is sum, inverse is negative, identity is zero, and powers are natural multiples.
This changes no objects, hypotheses or cases.

Clause-by-clause correspondence:

- A commutative monoid Q: `{Q : Type u} [CommMonoid Q]`, with arbitrary explicit universe u.
- Q is fine saturated: `hQ : IsFineSaturatedMonoid Q`, reusing the predicate from
  `Sheaf.AlgebraicGeometry.LogRegularPair`, available through the recorded fs-log dependency.
  Its three clauses are finite generation, injectivity into the canonical Grothendieck group,
  and positive-power root closure of the image in that group. No torsion-freeness or
  sharpness of Q is assumed.
- F is a submonoid: `F : Submonoid Q`; the face condition is
  `hF : ∀ a b : Q, a * b ∈ F → a ∈ F ∧ b ∈ F`.
- Q^gp is `Algebra.GrothendieckGroup Q`, with canonical map
  `Algebra.GrothendieckGroup.of`. Its source and full universal-property lift were read.
- Q_F is the existing `Algebra.faceLocalization Q F` from
  `Sheaf.TraceFormula.FaceLocalizationFs`. Its carrier is exactly the elements
  `of q * (of f)⁻¹` for q in Q and f in F, so it is the specified subset inside Q^gp.
- F^gp is `Algebra.faceGeneratedSubgroup F`, defined as
  `Subgroup.closure (GrothendieckGroup.of '' (F : Set Q))`.
- Q_F is fs: the first conclusion is
  `IsFineSaturatedMonoid (Algebra.faceLocalization Q F)`.
- Its units are exactly F^gp: the second conclusion is equality of submonoids of Q^gp,
  `(IsUnit.submonoid (Algebra.faceLocalization Q F)).map
  (Algebra.faceLocalization Q F).subtype = (Algebra.faceGeneratedSubgroup F).toSubmonoid`.
  Equality includes both containment directions and explicitly includes every element
  of the generated subgroup, not merely those already known to belong to Q_F.
- R = Q_F/F^gp is `Algebra.faceSharpening F`. It is the actual congruence quotient
  by `Con.ker (Algebra.faceLocalizationQuotientMap F)`. The map whose kernel is taken
  is the inclusion of Q_F followed by `QuotientGroup.mk'` for F^gp. Thus two
  representatives are identified exactly when their ratio belongs to F^gp, as required.
- R is fs: `IsFineSaturatedMonoid (Algebra.faceSharpening F)`.
- R is sharp: `∀ r : Algebra.faceSharpening F, IsUnit r → r = 1`.
  The identity is a unit in every monoid, so this states that it is the only unit.
- The canonical map R → Q^gp/F^gp is `Algebra.faceSharpeningMap F`, the actual
  `Con.kerLift` of the preceding map. Its injectivity is asserted explicitly by
  `Function.Injective (Algebra.faceSharpeningMap F)`.
- The identification of R^gp with Q^gp/F^gp is
  `Function.Bijective (Algebra.faceSharpeningGroupMap F)`. This map is specifically
  `GrothendieckGroup.lift (faceSharpeningMap F)`, so it extends the canonical map,
  rather than asserting existence of an unrelated group isomorphism.
- Finite freeness of R^gp is
  `∃ r : ℕ, Nonempty (Module.Basis (Fin r) ℤ
  (Additive (Algebra.GrothendieckGroup (Algebra.faceSharpening F))))`.
  The Additive tag equips the multiplicatively presented abelian group with its
  canonical additive structure and integer module structure; a basis gives exactly
  existence and uniqueness of the finite integer-coordinate expressions.

Dependencies used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup` is the recorded module for
  `def-trf-fs-log-blowup`. It uses `AlgebraicGeometry.IsFineSaturatedMonoid` from its
  public dependency `LogRegularPair`; the predicate and the relevant fs-chart declaration
  and docstrings were read. The full log-blowup definition is not duplicated here.
- `Sheaf.TraceFormula.FaceLocalizationFs`: `Algebra.faceLocalization`,
  `Algebra.faceLocalizationGroupMap`, `AlgebraicGeometry.faceLocalization_fineSaturated`.
  The already-landed node `lem-trf-face-localization-fs` is added to stmt_deps because
  the statement now uses its concrete localization. It was already a proof dependency.
- Proof imports are `Sheaf.AlgebraicGeometry.FaceLocalizationUnits`
  (`Algebra.isAddUnit_addLocalization_iff_face`),
  `Sheaf.AlgebraicGeometry.FaceSubgroupSaturated`
  (`AddSubmonoid.face_subgroup_saturated`), and
  `Mathlib.LinearAlgebra.FreeModule.PID`
  (`Module.basisOfFiniteTypeTorsionFree'`, the Mathlib match of
  `lem-trf-fg-torsionfree-group-free`). Their signatures and docstrings were read.
  The additive statements are applied to the additive tag of Q during stage 3.
- Mathlib provides the actual subgroup closure, group quotient, congruence kernel,
  quotient monoid, induced map, canonical group completion and basis type.
  The statement imports their definitions publicly; the PID theorem is a proof import.

Source checked directly in the supplied ILO PDF: VIII 3.1.1 defines sharpening as the
quotient by units; VIII 3.1.2 realizes integral localization in the group completion;
VIII 3.1.17 says saturation commutes with localization and sharpening. VI 1.6 uses
sharp fs characteristics, and VI 3.7(a) states finite generation and torsion-freeness
of their group completion. The theorem docstring carries all six steps of the node's
proof, including the named proof dependencies.

Edge cases checked mathematically:

- The trivial monoid has trivial localization and quotient and admits the rank-zero basis.
- F = Q gives Q_F = Q^gp, every localized element is a unit, R is trivial and r = 0.
- If Q is a group, the face axiom forces F = Q; the previous case applies.
- For sharp Q and the identity face, Q_F = Q and the sharpening is Q itself.
- In additive notation, Q = N² with a coordinate face has localization Z × N,
  unit subgroup Z × {0}, quotient N and rank one.
- In additive notation, Q = (Z/2Z) × N with its full unit face is permitted:
  its group completion has torsion, but R = N has torsion-free rank-one completion.
  The statement imposes no unwanted torsion-free hypothesis on Q.
- The empty set is not a submonoid; no face or rank case is excluded by an artificial
  Nonempty or positive-rank assumption. All structures remain in the same arbitrary
  universe u; no equality between independent universes is imposed.

Searches made before writing:

- `msearch.py`, LeanFinder: "Localization of a fine saturated monoid at a face and
  quotient by units is sharp fine saturated with finite free group completion".
  Eight results included localization finite generation, group-completion finite
  generation and unrelated ring localization; none states the full theorem.
- `msearch.py`, Loogle: `"GrothendieckAddGroup", "FG"`. One result was
  `Algebra.GrothendieckAddGroup.instFG`; it does not address faces or sharpening.
- `msearch.py`, grep: `sharpening|sharpification|FineSaturated|faceLocalization`.
  No Mathlib hits.
- `msearch.py`, LeanSearch: "The sharp quotient of a fine saturated monoid localized
  at a face has a finite free abelian group completion". Eight hits concerned
  additive localization, localized module finiteness and free abelian groups; no match.
- `rg` in upstream WeilConjectures and project lean/Sheaf for
  `faceLocalization|sharpening|sharpification|fs_face|FineSaturatedMonoid` found
  the shared fs predicate, the landed localization construction and its theorem,
  the units and face-subgroup lemmas, and consumers discussing this item.
  It found no complete sharpening statement or canonical sharpening maps.
- `rg` for the item id in upstream WeilConjectures found no existing statement.
- Exact names `faceGeneratedSubgroup|faceSharpening|fs_face_sharpening` were checked
  in upstream WeilConjectures, Mathlib, lean/Sheaf and dag/lean_names_upstream.json:
  no prior declarations were found.

Validation: scompile.py compiled the delivered file cleanly as both a sandbox file
and its library module path; no error or warning. Every variable and universe is
explicit, and the only postponed proof is the item's named theorem. The helpers
contain actual Mathlib constructions, with no sorry or existence choice of data.

## Second reading by Q88

Author's self-check only; the maintainer performs the independent review required
for direct worker delivery. Reopened the node and final module and checked all
three hypotheses and each of the seven conclusion clauses against the correspondence
above. The units conclusion was strengthened during drafting to exact equality of
embedded submonoids, so it visibly includes all of F^gp. The localization reuses the
published declaration rather than introducing another version. The quotient kernel
is exactly equality modulo F^gp, and its group map extends the specified canonical
map by construction. Rank zero and torsion in the original unit group remain allowed.
No mathematical correction to the node was needed.
