## Worker report

The module Sheaf.RingTheory.NoetherianKoszulAugmentationProZero states
ExteriorAlgebra.noetherian_koszul_augmentation_pro_zero, with sorry and no new definitions.
The mathematical statement is unchanged. Its stmt_deps gains the landed definition
node def-weil-pbc-koszul-complex, whose actual declaration is reused.

Hypotheses and clauses:

- The commutative Noetherian ring is `(A : Type u) [CommRing A] [IsNoetherianRing A]`.
  The chosen size of D(A) is `[HasDerivedCategory.{w} (ModuleCat.{u} A)]`.
- A finite list is `(r : ℕ) (a : Fin r → A)`, including r=0. The ideal I is literally
  `Ideal.span (Set.range a)` throughout, without a separate ideal parameter.
- All positive levels are indexed by m : ℕ with exponent m+1. Thus no level is omitted.
- Q is the existing `koszulComplex A r (fun i ↦ a i ^ (m+1))`, extended by
  `ComplexShape.embeddingDownNat` to integer cochain degrees. Its n-th exterior power
  is the tensor basis indexed by n-element increasing subsets. Contraction deletes
  the j-th wedge factor with sign (-1)^(j-1), exactly the signed total tensor
  differential of the node. The extension sends chain degree n to cochain degree -n.
  This is the project's established exterior Koszul model, not a second construction.
- The existential ε is a chain map to the degree-zero single complex on A/I^(m+1).
  Its degree-zero component is `mkQ.comp zeroEquiv.toLinearMap`; every other component
  is forced to be zero by the target single complex. This is the quotient augmentation.
- The existential t m k h is a chain map from level k to level m, with its component
  in every degree n fixed to `exteriorPower.map n` of the diagonal whose i-th entry
  is a_i^(k-m). On each wedge it multiplies by the product of these entries. In
  degree zero it is identity, in degree one it is the required multiplication.
- The quotient transition q is pinned by `mkQ ≫ (q m k h).f 0 = mkQ` for the two
  respective ideal powers. Surjectivity of the first quotient map determines its
  degree-zero component uniquely. All other components vanish. These are the
  canonical quotient transitions, not arbitrary morphisms.
- The existential hc states the exact strict square for each m≤k after extension.
  `homotopyCofiber.mapArrowHom` applied to `Arrow.homMk` with hc is the strict cone
  map. Its construction has the two specified maps on the diagonal summands; it
  does not pick a noncanonical triangulated filler.
- `∀ m, ∃ k h, DerivedCategory.Q.map (...) = 0` is exactly eventual vanishing of
  these cone transitions in D(A). Indices translate to the node's k+1≥m+1≥1.

The existence binders state the node's claim that the component formulas define
strict morphisms. They do not add hypotheses: maps are explicitly pinned by those
formulas, and hence unique. Identity and composite transition laws follow from the
same formulas (exterior powers of diagonal products and quotient surjectivity).
The cone maps are consequently the tower maps mentioned in the node.

Dependencies read and used:

- def-weil-pbc-noetherian-ring: Mathlib.RingTheory.Noetherian.Defs,
  IsNoetherianRing (every ideal finitely generated).
- def-pc-tensor-complex-sheaves: Mathlib.Algebra.Homology.BifunctorShift,
  CochainComplex.mapBifunctor; read its signature and docstring. Its total tensor
  sign convention is rendered by the existing exterior contraction model, not
  by a new tensor operation. The recorded module is imported.
- def-weil-abstract-derived-category: Mathlib.Algebra.Homology.DerivedCategory.Basic,
  HasDerivedCategory, DerivedCategory and DerivedCategory.Q.
- Added landed dependency def-weil-pbc-koszul-complex: Sheaf.Paper.KoszulComplex,
  ExteriorAlgebra.koszulComplex and koszulBoundary. Read the full construction and
  contraction docstrings. The KoszulOpenSystem power maps were inspected as well;
  that module builds negative tails and scheme objects, rather than the full
  ordinary-module complexes here, so its specialized objects are not substituted.
- Proof dependency lem-weil-pbc-artin-rees: imported Mathlib.RingTheory.Filtration,
  Ideal.exists_pow_inf_eq_pow_smul (recorded Mathlib match). The bounded-derived-tower
  proof dependency has no lean record yet, so there is no available module to import.

Edge cases: r=0 gives I=0 and Q=A[0] under zeroEquiv, so the augmentation cone is
acyclic. Zero generators, unit generators, zero ring, and redundant generators are
allowed: no regular sequence or nonzero assumption appears. The first level is
exponent one. Equal levels give diagonal entries a_i^0=1 and identity quotient
maps. Arbitrary ring universe u and derived morphism universe w are explicit;
there are no implicit variables and no restriction to finite or nonzero rings.

Searches made:

- msearch.py leanfinder: "Noetherian Koszul augmentation cones form a pro zero tower
  in the derived category" returned eight generic mapping-cone, derived-fraction,
  projective and injective results; none states this Koszul tower assertion.
- msearch.py loogle: `"Koszul"` returned zero hits.
- msearch.py grep: `Koszul|proregular` returned a local-cohomology TODO, a
  regular-sequence TODO and unrelated Koszul connections. No theorem matches.
- rg in the source WeilConjectures tree for Koszul and the item id: no item-id match;
  projective-line Koszul sequences and monoidal sign conventions are different.
- rg in lean/Sheaf for Koszul, koszulComplex, KoszulOpenSystem and constructions:
  found and reused the exterior Koszul complex; inspected ShiftedKoszulAugmentation
  and KoszulOpenSystem to avoid confusing their tails and scheme images with Q.
- Inspected the upstream name index for Koszul; no matching theorem was found.

Source reading: more-algebra.tex lemma-sequence-Koszul-complexes (0921) and
proposition-noetherian-naive-completion-is-completion (0922), including Artin--Rees
and the cofinality of generator powers and ideal powers; derived.tex
lemma-essentially-constant-cohomology (0G3B). The docstring records all five proof
steps, including the necessary final upgrade from cohomology to derived maps.
No statement dispute or correction is needed. No new definition nodes or dependency
replacement modules are added.

Validation: server scompile.py compiled the delivered file cleanly in 1.4 seconds,
with nice 19, two threads and the 60-second per-file limit. No local compiler ran.

## Second reading by NB

I read the node and its five proof steps independently against the actual module,
Stacks more-algebra.tex, Situation 0BKC and Tags 0921/0922, and derived.tex,
Tag 0G3B. The source assumes a commutative ring and a finite generating list;
Noetherianity is added in 0921. No local, domain, regular-sequence, or characteristic
hypothesis is present. The ideal-power formulation follows the cofinality argument
in 0922; the node supplies the explicit strict-cone calculation.

Object/hypothesis/conclusion inventory and matches (all pass):

- Ring A: `(A : Type u) [CommRing A] [IsNoetherianRing A]`. Mathlib's
  `IsNoetherianRing` is `IsNoetherian A A`; `isNoetherian_def` says every submodule
  (hence ideal) is finitely generated. This is exactly the dependency node.
- Finite list and generated ideal: `(r : ℕ) (a : Fin r → A)` and
  `Ideal.span (Set.range a)`. No independent ideal or generation assumption appears.
- Positive levels: every `m : ℕ` denotes the node's level `m+1`. All positive levels
  occur, and `m ≤ k` is equivalent to the required order on positive levels.
- Q_m: `koszulComplex A r (fun i ↦ a i ^ (m+1))`, extended by
  `ComplexShape.embeddingDownNat`. I opened the dependency node and its module:
  terms are exterior powers of `Fin r →₀ A`, differential is contraction at the zero
  quadratic form. In the increasing-subset basis its signs are precisely deletion
  signs in the node's total tensor product. The embedding explicitly sends n to -n.
  Exterior powers above r are zero objects, so this model has the required support
  up to the canonical zero identifications. This is the existing Koszul notion.
- D(A): `[HasDerivedCategory.{w} (ModuleCat.{u} A)]` and `DerivedCategory.Q.map`.
  I read `HasDerivedCategory`, `DerivedCategory`, and `Q`: this is localization of
  integer cochain complexes at quasi-isomorphisms. The binder chooses morphism size,
  not a mathematical restriction; the standard localization exists.
- Augmentation: existential `ε m` targets `ChainComplex.single₀` on A/I^(m+1),
  and its degree-zero component is `mkQ.comp zeroEquiv.toLinearMap`. Other target
  terms are zero, so the formula fixes the entire chain map. Existence records the
  claimed construction without adding an assumption.
- Koszul transitions: the formula for every `(t m k h).f n` is the n-th exterior
  power of the diagonal with entries a_i^(k-m). On an increasing wedge it gives
  exactly the product over its indices; in degree zero it is identity. Thus all
  components, including higher degrees, are pinned. Identity and composite laws
  follow from these formulas; omitting redundant laws does not allow another tower.
- Quotient transitions: `mkQ ≫ (q m k h).f 0 = mkQ` fixes the canonical reduction
  A/I^(k+1) → A/I^(m+1), since the source quotient map is surjective. The other
  components have zero source and target. No arbitrary transition is allowed.
- Strict morphism of towers: `hc m k h` is precisely t ≫ ε_m = ε_k ≫ q after
  extension. I opened `homotopyCofiber.mapArrowHom`: it takes a morphism of arrows
  and constructs its induced cone map. Its identity/composition lemmas show these
  are the actual strict cone transitions, with no free homotopy or triangle filler.
- Pro-zero conclusion: `∀ m, ∃ (k : ℕ) (h : m ≤ k), DerivedCategory.Q.map
  (homotopyCofiber.mapArrowHom ... (Arrow.homMk ... (hc m k h))) = 0`.
  This has exactly the node's quantifier order and asserts zero in D(A), rather
  than only a zero map on cohomology.

I also opened the recorded `CochainComplex.mapBifunctor` declaration: it totals the
bicomplex, as required by the tensor dependency. No replacement tensor notion is
introduced. `Ideal.exists_pow_inf_eq_pow_smul` in Filtration has the Noetherian,
finite-module and submodule inputs used by the proof. The bounded-derived-tower
node has no Lean record, so no proof-dependency module is available to import.
There are no new definition nodes or dependency replacement modules to audit.
The sole delivered theorem has proof `sorry`; there is no new data definition.
The source/blueprint docstrings and all five natural-language proof steps are present.

Edge cases: r=0 is included, with E=0, Q canonically A[0], I=0 and acyclic cone.
The first level is m=0 (exponent one), never exponent zero. Equal levels have
entries a_i^0=1 and identity quotient maps. Zero, unit, repeated and nilpotent
entries and the zero ring are allowed. In characteristic two the same alternating
formula applies with -1=1. Universes u and w are explicit, all indices are bound,
and no field or nontriviality assumption appears. Empty schemes are inapplicable
because every object here is an ordinary module complex.

Independent searches used different queries from the author:
`msearch.py leanfinder "Weak proregularity of a finitely generated ideal in a
Noetherian ring via Koszul augmentation mapping cones"` returned eight results
about regular sequences, Noetherian modules and ordinary completion, none matching.
`msearch.py loogle '"pro_zero"'` returned zero hits. Direct rg searches for weak
proregularity, Koszul augmentation, and the declaration name across Mathlib,
upstream WeilConjectures, lean/Sheaf and the upstream name index found no matching
statement. I inspected `exists_koszul_quotient_augmentation`: it assumes Koszul
regularity and targets the generated ideal quotient, so it cannot replace this
Noetherian tower assertion. `KoszulOpenSystem` instead uses the shifted negative
tail augmented to A, as its actual signatures confirm. Upstream projective-space
Koszul sequences and Mathlib's local-cohomology/regular-sequence TODOs also do not
state this assertion.

No mathematical mismatch was found; no Lean or node change was necessary.
The second reading adds this independent inventory and verification evidence only.
The node's `lean.statement` was checked verbatim against the delivered signature.
Validation uses only server scompile.py with the mandated resource limits; the
complete delivery is also checked by deliver2.py before pushing.
