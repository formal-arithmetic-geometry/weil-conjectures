## Worker report

Repair of return L at immutable head 6bc244c50988. This is now a stage-2 delivery:
`lean/Sheaf/AlgebraicGeometry/SmoothProperFiniteCohomologyLocalSystem.lean` states
`AlgebraicGeometry.Etale.finite_localSystem_higherDirectImage_smooth_proper`, with one
`sorry` proof. No new definitions or helper nodes are delivered. The sandbox initially
contained only dispatcher brief marker files; the returned stage-1 split was not retained
as a delivery. The node was copied afresh from the live read clone. Only its `lean` field
changes: its nine proof steps, proof_deps, split_report, statement and stmt_deps are intact.
The old stage-1 repair note was read and is superseded for this assignment by the explicit
stage-2 return instruction; no re-split is attempted here.

Clause-by-clause correspondence:

- Schemes and the morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Smooth and proper: `[Smooth f] [IsProper f]`, using the recorded Mathlib classes.
- Prime ell and F_ell = Z/ell Z: `(ell : ℕ) [Fact ell.Prime]` and
  `ULift.{u + 1} (ZMod ell)`. The lift changes only the universe, retaining the prime-field
  ring and module structures, and permits the small etale site's coefficient size u+1.
- Invertibility on S: `hunit : ∀ s : S, IsUnit (ell : S.presheaf.stalk s)`, literally
  invertibility in each local ring of S.
- The sheaf F: `Sheaf X.smallEtaleTopology
  (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))`. This is the established constant-coefficient
  encoding of module sheaves (the direct-image node explicitly permits ModuleCat-valued
  sheaves). `ringedSiteModules` is imported from its recorded dependency; it is not copied.
  The existing `WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence`
  gives the canonical comparison to modules over the constant ring sheaf, as used by the
  recorded proof dependency ModuleCohomologyConventions. No arbitrary action is supplied.
- The input local finite-dimensional models: `hF` gives a `Scheme.Cover` for
  `Scheme.etalePrecoverage X`. For each member it gives a module M, `Module.Finite` over
  the lifted prime field, and `Nonempty (F.over ... ≅ (constantSheaf ...).obj M)`.
  The restriction uses the localized small etale site. These are module-linear
  isomorphisms, not isomorphisms merely of underlying abelian sheaves. A finite module
  over a field is precisely a finite-dimensional vector space.
- Every nonnegative integer degree: `(q : ℤ) (hq : 0 ≤ q)`. There is no upper bound.
- R^q f_* F: `DerivedCategory.Plus.singleFunctor _ 0` puts F in degree zero,
  `rightDerivedLowerStarPlus (ModuleCat ...) f` is the recorded bounded-below derived
  direct image, and `DerivedCategory.Plus.homologyFunctor _ q` takes its q-th cohomology.
- The conclusion gives an etale cover of S and for each member a module N with
  `Module.Finite` and a module-sheaf isomorphism from the restriction of that R^q f_* F
  to its constant sheaf. This is exactly the requested local-system conclusion.
- No Noetherian, field-base, finite-type-over-field, connectedness, nonemptiness,
  fixed-relative-dimension, global rank or uniform cover hypothesis occurs.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `AlgebraicGeometry.Smooth`.
- Mathlib.AlgebraicGeometry.Morphisms.Proper: `AlgebraicGeometry.IsProper`.
- Mathlib.AlgebraicGeometry.Sites.Etale: `Scheme.smallEtaleTopology`,
  `Scheme.etalePrecoverage`; WeilConjectures.ConstructibleSheaf.Defs:
  `Scheme.Cover.etalePrecoverageToEtale` (the existing cover-to-site-object interface).
- Sheaf.CategoryTheory.RingedSiteModules: `CategoryTheory.ringedSiteModules`, the
  general ringed-site category. Constant coefficients use the canonical ModuleCat
  encoding already selected by the direct-image node and its recorded upstream API.
- Mathlib.CategoryTheory.Sites.ConstantSheaf: `CategoryTheory.constantSheaf`.
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs: `Etale.lowerStar`.
- WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence:
  `Etale.rightDerivedLowerStarPlus` (not located in the primary module of the old record,
  but its second recorded declaration has this existing source module).
- WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients supplies the
  sheafification instances for ModuleCat in the required universe.

All recorded statement-dependency modules are public imports. Stated proof-dependency
modules are plain imports unless already public statement imports; duplicate module paths
are imported once. `lem-weil-pbc-qcqs-over-affine` is unstated and has no module to import;
`def-weil-pbc-scheme-conventions` is a convention with no module. Every other recorded
proof-dependency module is imported, including the finite-local-system limit-descent lemma.
The theorem docstring carries all nine live proof steps, including the arbitrary-base
Noetherian approximation and proper-base-change argument, with their dependency IDs.

Edge cases checked by reading the signature and source: q=0 is included; negative degrees
are outside this node's assertion; ell=2 is included; ell=0 and ell=1 are excluded only
because they are not primes; no prime is excluded independently of the unit hypothesis.
The zero sheaf and zero-dimensional local models are allowed by Module.Finite. The empty
scheme is allowed (its empty cover has vacuous local-model conditions), and no Nonempty
instance is required. Disconnected and non-quasi-compact bases are covered with different
local models on different cover members. No global bound on the dimensions is asserted.

Searches (2026-10-23; raw msearch results are in sandbox searches.jsonl):

- LeanFinder: “smooth proper morphism higher direct image of finite locally constant
  F_ell sheaf is finite locally constant”: eight unrelated condensed-sheaf hits; no match.
- Loogle: “AlgebraicGeometry.Etale.rightDerivedLowerStarPlus,
  CategoryTheory.constantSheaf, Module.Finite”: unknown project identifier, no result.
  Direct source inspection located rightDerivedLowerStarPlus as above.
- LeanSearch: “Higher direct images of a finite locally constant sheaf under a smooth
  proper morphism of schemes are finite locally constant”: eight hits, including
  Sheaf.isConstant_iff_mem_essImage, but no matching theorem.
- msearch grep, Mathlib AlgebraicGeometry: `smooth.*proper|[Ll]ocally[Cc]onstant`:
  eleven hits (smooth morphisms, flat rank, elliptic curves), no matching statement.
- rg in lean/WeilConjectures and lean/Sheaf for
  `finite.*[Ll]ocal[Ss]ystem|smooth.*proper.*[Ll]ocal|finite.*cohomology.*local`:
  found Etale.BaseChangeTheorems.SmoothProperLocallyConstant's
  `isFiniteLocallyConstantSheaf_homology_rightDerivedLowerStar_of_smooth_of_isProper`.
  Its full signature requires a finite-type base over a field, so it is not this node.
  Its pro-etale counterparts likewise do not supply this arbitrary-base etale statement.
- rg for this item's ID in lean/WeilConjectures gave no match; references in Sheaf are
  downstream proof descriptions, not a declaration stating this node.
- rg for the proposed full declaration name found no existing declaration.

Source read: literature/stacks-project/more-etale.tex, proposition-loc-cst-torsion
(lines 4785–4854), Tag 0GLI. It permits an arbitrary base and explicitly reduces it to a
Noetherian base by affine approximation. The prime-field specialization here is valid:
F_ell is Noetherian and each stalk is ell-torsion, with ell invertible on S.
No statement correction or STATEMENT-DISPUTED issue remains.

Validation: scompile.py Q129 on the delivered module passed in both sandbox and library
modes (20.6 s and 9.0 s). No errors or warnings were printed. The signature is recorded
verbatim in the node lean record; `autoImplicit false` and explicit universe u prevent
unbound implicit variables. Dry-run and delivery outcomes are recorded below after running.

## Second reading by Q129

This is a separate second pass by the same dispatched worker, not an independent agent:
the dispatcher explicitly forbids starting other agents. I reopened the live node and the
whole Lean file and compared their binders and conclusion. The match is as follows:
“smooth proper” is exactly the two morphism instances; “ell prime invertible on S” is
Fact ell.Prime together with pointwise IsUnit; “sheaf of F_ell-modules on X_et” is the
ModuleCat-valued Sheaf over the recorded smallEtaleTopology; “etale locally isomorphic to
a constant finite-dimensional vector space” is the explicit cover plus Module.Finite plus
module-linear constant-sheaf isomorphism in hF. The conclusion repeats that exact condition
for the homology of the bounded-below derived pushforward, with base S instead of X.
The two degree binders match “integer q >= 0”. The cover and model can depend on q and the
cover member, as they must; the statement asserts no global constant rank. The empty base,
zero model, degree-zero and non-Noetherian cases remain admitted.

The returned defects H1 and H2 are repaired: there is a real module, a complete lean record,
and both report sections. The live nine-step proof, proof_deps and split_report are
unchanged. There are no statement-only helper nodes from the refused stage-1 re-split.
The stronger field-base hypothesis of the existing upstream theorem was specifically
checked and rejected as an existing:true match. During this second pass I repaired word
wrapping in the proof docstring so dependency IDs are not split at hyphens. No mathematical
mismatch was found, and no signature change was needed. One named theorem is postponed
with sorry; no definition has postponed data.
