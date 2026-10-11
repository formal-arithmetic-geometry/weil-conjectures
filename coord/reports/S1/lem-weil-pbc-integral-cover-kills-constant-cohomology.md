## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology` states
`AlgebraicGeometry.Etale.exists_isFinite_surjective_constant_cohomology_eq_zero`, with
`by sorry`. It introduces no definitions. The node is unchanged except for `lean`.

The source was read at https://stacks.math.columbia.edu/tag/09ZD (Lemma 59.80.9,
part (2), and its proof). The local literature checkout is absent on this machine.
The source agrees with every hypothesis and conclusion of the node. The theorem docstring
carries the seven steps of the node's proof, with the dependency IDs, for stage 3.

Hypothesis and clause matching:

- The affine scheme X is `{X : Scheme.{u}} [IsAffine X]`.
- A closed subscheme Z of X is `{Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]`.
  This includes every closed immersion, not only a chosen quotient spectrum.
- The finite abelian group M is `(M : AddCommGrpCat.{u + 1}) [Finite M]`.
  Bundling supplies its abelian group structure; finiteness is of its underlying type.
- Its constant abelian sheaf on Z's small etale site is
  `(constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M`.
- The integer q ≥ 1 is `(q : ℕ) (hq : 1 ≤ q)`. All positive integers are natural
  numbers; there are no omitted negative degrees satisfying the node's inequality.
- The class ξ is the argument of type `Sheaf.H` of that constant sheaf in degree q.
- The existential cover X' → X is `∃ (Y : Scheme.{u}) (f : Y ⟶ X)`.
- Finite, surjective and finite presentation are respectively `IsFinite f`,
  `Surjective f`, and `LocallyOfFinitePresentation f`. A finite morphism is affine,
  hence quasi-compact and quasi-separated, so this conjunction is precisely finite
  presentation, as in the comparison clause of def-sbc-locally-finite-presentation.
- The fibre product X' ×_X Z is `pullback f i`; its projection to Z is
  `pullback.snd f i`, not the other projection.
- Pullback of ξ is `cohomologyMap (pullback.snd f i) ... q ξ`.
- Identification of inverse-image constant coefficients with the constant sheaf on
  `pullback f i` is explicitly the hom component at M of
  `Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (pullback.snd f i)`.
  `Sheaf.H.map` transports the pulled-back class along that sheaf isomorphism.
- The final equation `= 0` lies in `Sheaf.H` of the constant sheaf on the fibre product.
  Thus the statement includes the constant-coefficient identification in the node,
  rather than leaving its target coefficients implicit.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `AlgebraicGeometry.IsAffine`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (def-weil-closed-immersion).
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`
  (def-weil-pbc-constant-sheaf).
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`
  (def-weil-finite-integral-morphism).
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`
  (def-weil-surjective-morphism).
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` (the Mathlib leaf
  def-sbc-locally-finite-presentation has mathlib_match, so requires no lean record).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback` and `pullback.snd` (def-pc-fibre-product).
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`:
  `AlgebraicGeometry.Etale.cohomologyMap` (def-weil-pbc-cohomology-pullback).
- `WeilConjectures.ConstructibleSheaf.Defs`:
  `AlgebraicGeometry.Scheme.upperStarConstantSheafIso`
  (lemma-constructible-pullback-constant; read the slopmaster2 declaration).
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`: `CategoryTheory.Sheaf.H`
  and `Sheaf.H.map`. This is the Ext-based cohomology encoding explicitly permitted
  by the recorded lean notes of def-weil-pbc-etale-cohomology and
  def-weil-pbc-cohomology-pullback. The recorded `Etale.cohomology` and
  `rightDerivedGlobalSections` in `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
  were also read: their agreement with this Ext encoding is the existing stage-3 bridge,
  not a new private cohomology definition. No duplicate dependency module is needed.

The four direct imports supply all of the above declarations transitively. Every universe
and variable is bound explicitly. There is no local notation, instance or private definition.

Edge cases checked before writing: q = 0 is correctly excluded (the nonzero degree-zero
constant section need not die on a surjective cover); q = 1 is included. The zero group and
zero class are included and can use the identity cover. Empty Z is allowed, as is empty X:
closed immersion into empty X forces Z empty and the identity cover is still available.
No Noetherian, characteristic, field, henselian-pair or nonempty hypotheses are imposed.
The coefficient universe u+1 admits every finite abelian group up to isomorphism; the cover
can be taken in the scheme universe u since finite finitely presented algebras over a
u-small affine ring are u-small. No arbitrary small test universe is quantified over.

Searches made (2026-10-11):

- msearch.py leansearch: "etale cohomology constant finite abelian group killed by finite
  surjective cover". Service unavailable, Internal Server Error; no verdict drawn.
- msearch.py leanfinder: "A positive degree etale cohomology class with finite constant
  abelian coefficients on a closed subscheme of an affine scheme is killed by a finite
  surjective cover of finite presentation". Eight hits, including
  `AlgebraicGeometry.exists_appTop_map_eq_zero_of_isAffine_of_isLimit` and its variants,
  etale/smooth loci and cotangent modules. These are structure-sheaf section or ring
  statements, not this etale cohomology assertion.
- msearch.py loogle: `CategoryTheory.Sheaf.H, AlgebraicGeometry.IsFinite`. Zero hits.
- msearch.py grep: `cohomologyMap|efface|Gabber`, Mathlib/AlgebraicGeometry. Zero hits.
- rg over source `WeilConjectures/` and project `lean/Sheaf/` for the node ID: no
  existing statement. Searches for finite-cover killing, 09ZD and constant cohomology
  found Gabber.lean and related curve statements, and GabberConstantH1Vanishing.lean.
  Read Gabber.lean's finite-stage and finite-cover declarations: they concern a chosen
  limit system or a henselian pair with constructible module sheaves, and do not assert
  this statement for every affine X, closed Z and finite abelian M. The H1 vanishing
  statement concerns absolutely algebraically closed rings, also not this assertion.
- Read and searched the source and Mathlib declarations listed above to verify the
  constant sheaf, comparison isomorphism, cohomology map and morphism predicates.

Validation: scompile.py on the server compiled the 66-line module in 2.4 seconds,
exit code 0, without warnings. No node faults or STATEMENT-DISPUTED issues found.
The independent second reader must still read this statement and deliver it.


## Second reading by S1

Independent second reading, 2026-10-12. I opened the sandbox node and the entire
66-line Lean module, all ten statement-dependency nodes, and the source declarations
listed below. No statement correction, new definition node, or dependency module is
present or needed. The existing Lean statement is retained verbatim.

Source check: I read the raw Stacks `etale-cohomology.tex` at
https://raw.githubusercontent.com/stacks/stacks-project/master/etale-cohomology.tex,
label `lemma-integral-cover-trivial-cohomology`, its proof, and the beginning of
section `section-strictly-henselian-local-rings`. I also checked the rendered
[Tag 09ZD](https://stacks.math.columbia.edu/tag/09ZD), part (2). The section's
introductory discussion imposes no standing strictly henselian hypothesis on this
lemma: this lemma explicitly starts with an arbitrary affine scheme. Its part (2)
agrees with the node; no Noetherian, separated, field, characteristic, or henselian
assumption is missing. The source proof passes through an integral cover, finite
finitely presented approximations, and continuity of cohomology, as the node does.

Object, hypothesis, and conclusion checklist (the node's statement in order):

1. Scheme X, affine: `{X Z : Scheme.{u}} [IsAffine X]`. PASS. Mathlib `Scheme`
   is a locally ringed space locally isomorphic to spectra; `IsAffine` says its
   canonical map to the spectrum of global sections is an isomorphism.
2. Closed subscheme Z of X: `(i : Z ⟶ X) [IsClosedImmersion i]`. PASS. The
   dependency's recorded class is a closed embedding with surjective stalk maps;
   this is the closed-subscheme notion, with no chosen quotient presentation.
3. Finite abelian group M: `(M : AddCommGrpCat.{u + 1}) [Finite M]`. PASS.
   The bundle provides precisely an abelian group; `Finite` is a property of its
   carrier, with no chosen enumeration or extra module structure.
4. Constant sheaf on the small etale site of Z:
   `(constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M`. PASS.
   The dependency's `constantSheaf` is the constant-presheaf functor followed
   by sheafification, not the generally nonsheaf constant presheaf.
5. Integer q >= 1: `(q : ℕ) (hq : 1 ≤ q)`. PASS. Every integer satisfying
   the source inequality is uniquely a positive natural number; no allowed
   degree is omitted.
6. A class xi in that cohomology group: the binder `ξ : Sheaf.H ... q`.
   PASS. I read `Sheaf.H` (Ext from the constant ULift integer sheaf),
   `Etale.cohomology`, and `rightDerivedGlobalSections`. The cohomology
   dependency's recorded `lean.note` expressly permits this source-wide Ext
   encoding and reserves its comparison with derived global sections for stage 3.
7. There exists a scheme X' and a morphism X' -> X:
   `∃ (Y : Scheme.{u}) (f : Y ⟶ X)`. PASS. The existential follows all
   of Z, M, q, and xi; the cover can depend on the given class.
8. The morphism is finite: `IsFinite f`. PASS. I read the recorded Mathlib
   class extending `IsAffineHom` and requiring finite maps on affine sections.
9. The morphism is surjective: `Surjective f`. PASS. I read the class:
   it means surjectivity on all underlying points.
10. The morphism is of finite presentation: `LocallyOfFinitePresentation f`
    together with `IsFinite f`. PASS. This is globally finite presentation:
    finiteness implies affine, hence quasi-compact (Morphisms/Affine.lean:58)
    and separated (Morphisms/Separated.lean:119), hence quasi-separated
    (Separated.lean:68). The dependency node's comparison clause defines finite
    presentation as locally finite presentation plus these two properties.
    No additional conjunct is needed, and none is lost.
11. Fibre product X' x_X Z and its projection to Z: `pullback f i` and
    `pullback.snd f i`. PASS. I opened `pullback` and both projection
    signatures; `snd` has codomain Z. Scheme pullbacks are already available.
12. Pullback of xi along that projection: `cohomologyMap (pullback.snd f i)
    ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) q ξ`.
    PASS. I read its section binders and definition: arbitrary scheme morphism,
    arbitrary abelian sheaf, degree n; no universal-homeomorphism hypothesis.
    It is the exact-inverse-image Ext map recorded by the pullback dependency.
13. Identify inverse-image coefficients with the constant sheaf on the fibre
    product: `(Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
    (pullback.snd f i)).hom.app M`, followed by `Sheaf.H.map ... q`.
    PASS. I read the isomorphism in ConstructibleSheaf/Defs.lean: its forward
    direction is `constantSheaf ⋙ upperStar ≅ constantSheaf` on the new scheme.
    `Sheaf.H.map` is covariant in the coefficient sheaf, so the direction is correct.
14. This class is zero in H^q of the constant sheaf on X' x_X Z: the final `= 0`.
    PASS. The preceding coefficient map has exactly that target. It asserts
    vanishing of the chosen class, not vanishing of the entire cohomology group.

Dependency audit: I read the actual signatures in Mathlib's Scheme, AffineScheme,
Morphisms/ClosedImmersion, Morphisms/Finite, Morphisms/UnderlyingMap,
Morphisms/FinitePresentation, Sites/ConstantSheaf, Limits/Shapes/Pullback/HasPullback,
and Sites/SheafCohomology/Basic, plus the source's
SixFunctors/Etale/UpperLowerStar/TopologicalInvariance,
SixFunctors/Etale/Derived/LowerShriek, and ConstructibleSheaf/Defs.
All ten dependency notions are supplied by those existing declarations. No private
copy, hollow data, auxiliary instance hypothesis, or missing notion was found.

Edge cases: q = 0 is excluded exactly as in the node; q = 1 is included.
The zero group and zero class are admitted. Empty X and empty Z are admitted;
a closed immersion into empty X forces empty Z. Identity covers suffice for
those degenerate cases. There is no index set in the statement, so no hidden
nonemptiness requirement. No restriction excludes characteristic p or groups
with p-torsion. Universe u is explicitly bound and arbitrary. Schemes and the
finite cover live in the same u; finite finitely presented algebras over a
u-small ring have u-small representatives. Every finite abelian group has a
representative in `Type (u + 1)`, the coefficient universe used throughout the
recorded small-etale-site API. There is no quantified small test universe and
no extra `HasExt`, sheafification, or abelian-category instance in the signature.

Independent searches, using words different from the worker's queries:

- msearch leansearch: `Finite surjective morphism annihilates positive degree
  etale cohomology with finite constant coefficients`. Service unavailable
  (Internal Server Error); no absence verdict is based on this service.
- msearch leanfinder: `A torsion constant etale cohomology class of positive
  degree on a closed affine subscheme vanishes after a finite finitely presented
  surjective base change`. Eight hits: etale/smooth loci, cotangent H1, and
  affine-limit structure-sheaf sections becoming zero. None is this assertion.
- msearch loogle: `"cohomology", "finite"`. Eleven hits, all finite cyclic
  group cohomology or Tate-complex finite-(co)limit statements. None is this assertion.
- rg in the full source WeilConjectures tree, project lean/Sheaf, Mathlib's
  AlgebraicGeometry and CategoryTheory/Sites trees, and dag/lean_names_upstream.json:
  `09ZD`, killing/constant/cohomology combinations, finite-cover/cohomology
  combinations, `annihilat`, `efface`, and the proposed full declaration name.
  No duplicate statement/name found. Part (1) is the project's
  Paper/IntegralCoverTrivialCohomology.lean; it gives an integral cover and whole
  cohomology vanishing, not a finite finitely presented cover killing one class.
  I opened the source SixFunctors/Etale/Gabber.lean signatures:
  `exists_cohomologyMap_eq_zero_of_isLimit` requires a supplied system and
  vanishing at its limit; `exists_isFinite_cohomologyMap_eq_zero_of_henselianRing`
  requires a henselian pair and constructible module sheaf and concludes unit
  monicity, not this arbitrary-affine surjective-cover statement. Neither is a
  replacement. An initial guessed `ProperBaseChange/Gabber.lean` path did not
  exist; `rg --files` located the actual module before its signatures were read.

Docstring and shape check: both docstrings cite Stacks 09ZD (2) and the exact
blueprint ID. The theorem docstring follows all seven proof steps in order,
including coefficient identification, ring/tensor-product continuity, finite-stage
vanishing, and surjectivity by factorization. Every theorem proof is `by sorry`;
there are no definitions or actual proofs in this delivery. All lines are at most
100 characters; the four imports supply the used morphism and cohomology APIs.
All variables/universes are explicitly bound. A direct text comparison confirmed
`lean.statement` equals the source signature verbatim, through the text before `:=`.

Mismatches and repairs: none. No correct Lean or node text was rewritten. The only
addition is this independent second-reading record.

Validation: the first compiler invocation used a repository-relative path and
failed before compilation because the module exists only in the sandbox; rerunning
with its absolute sandbox path compiled the 66-line module on the server in 2.6 s,
exit code 0, with no warnings. This was a path correction, not a compiler failure.
