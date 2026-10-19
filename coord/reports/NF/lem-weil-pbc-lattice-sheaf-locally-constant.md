## Worker report

The module `Sheaf.Paper.LatticeSheafLocallyConstant` states
`AlgebraicGeometry.ProEtale.integralLatticeSheaf_locallyConstant`, with `sorry`.
It includes the canonical coefficient, lattice-pair, image, quotient-presentation,
and matrix-lattice helpers introduced by this node, all listed in `lean.declarations`.
The additional postponed coefficient-sheaf axiom is the named
`isSheaf_latticeCoefficientPresheaf`; it supplies only the proof component of a
fully specified presheaf. It has the same owning blueprint id and a full proof
from Mathlib's fpqc continuous-function descent in its docstring. No module,
restriction map, coefficient function, or lattice data is chosen from an
unconstrained existence theorem.

Hypotheses and objects, clause by clause:

- Prime ell is `(l : ℕ) [Fact l.Prime]`; the finite extension is `(E : Type u)
  [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
- Its topology is not arbitrary. `WithAbs
  (Padic.coefficientExtensionAbsoluteValue l E)` equips precisely the underlying
  field with its recorded absolute value. `latticeCoefficientIntegers l E` is
  the comap of the recorded `Padic.coefficientExtensionIntegers l E` along the
  canonical `WithAbs.equiv`. It has the induced subring topology, as required.
  This is an explicit transport of the given field and valuation ring, not
  another valuation ring or an assumed topological field structure.
- `X : Scheme.{u}` is arbitrary. The site is `Scheme.ProEt.topology X` on
  `X.ProEt`, with object universe u+1 and morphism universe u unchanged.
- `latticeCoefficientPresheaf X T` has sections
  `CommRingCat.of (ULift C(V.left,T))`, pointwise operations, and the displayed
  precomposition ring homomorphisms. `latticeCoefficientSheaf` adds only its
  sheaf-condition proof. `latticeModuleRing` forgets commutativity for Mathlib's
  module-sheaf category. The integral coefficient map is postcomposition with
  the actual subring inclusion and its subtype continuity proof.
- `L` is a `SheafOfModules` over that rational continuous-coefficient ring;
  `[L.IsFiniteLocallyFree]` is the upstream general-site predicate. Its finite
  local generating families permit varying finite ranks and rank zero. No
  connectedness, noetherianity, nonemptiness or fixed rank is assumed.
- `IntegralLatticePair a L U` consists of its actual integral module sheaf,
  its finite local freeness, and
  `rationalization : changeOfRings (latticeScalarMap a U) module ≅ L.over U`.
  Thus alpha is an isomorphism of rational module sheaves, not just a map or a
  vector-space equivalence. `changeOfRings` is the recorded sheafified tensor.
- `IntegralLatticePair.Equivalent` is exactly existence of an integral module
  isomorphism `e` for which `changeOfRingsHom ... e.hom ≫ Q.rationalization.hom
  = P.rationalization.hom`. Both directions of the node's identification rule
  are retained.
- The existential sheaf `F` with the maps `c U` is an exact presentation of
  this quotient. `IsLatticeClassPresentation` requires that every section is
  represented by a pair and that two representatives have equal images if
  and only if they are equivalent. This is equivalent to a sectionwise
  bijection from the stated set of isomorphism classes; it does not identify
  extra pairs or merely assert nonemptiness of a sheaf.
- The same presentation specifies ALL restriction maps: for every `f : V ⟶ U`,
  the restriction of `c U P` equals `c V Q` if and only if the embedded images
  of P and Q agree on every object of the slice over V. `Over.map f` is the
  actual slice restriction, and `L.over` evaluates on the same underlying
  objects. The embedding is explicitly alpha applied to the sheafification
  image of `1 ⊗ m`. The node's first proof step identifies these embedded
  images with the original pairs; accordingly this is exactly inverse image
  on localized sites, rather than an arbitrary presheaf action. Identity
  restrictions also yield the stated criterion for equivalent pairs.
- For EVERY `U`, `n : ℕ`, and trivialization `e : L.over U ≅
  latticeFreeSheaf ... U n`, the conclusion supplies an isomorphism `k` from
  the constant sheaf of `integralMatrixCosets` on that slice to `F.over U`.
  `latticeFreeSheaf` uses Mathlib's finite coproduct of the coefficient unit,
  indexed by `ULift (Fin n)`. Thus it is precisely E_U^n.
- The subgroup in `integralMatrixCosets` is the range of the actual homomorphism
  `GL_n(A) → GL_n(E)` induced by the subring inclusion, and the quotient is
  `gH`, equivalently orbits of right multiplication. No normality is assumed.
  The value set is lifted to the section universe and then passed to the
  recorded `constantSheaf`, so this is the sheafification of a discrete
  constant presheaf, not the continuous-coefficient sheaf of a quotient space.
- The last iff normalizes `k` on every constant coset: its constant-sheaf unit
  section maps to `c U P` exactly when, on every slice object, the embedded
  image of P, expressed using e, equals `matrixLatticeImage ... g`.
  That image is explicitly all sums of columns of g with continuous integral
  coefficients. It is exactly g A_U^n, including the inclusion-induced
  rationalization alpha_g because the pair is determined by its embedding.
  This retains the canonical action of the isomorphism, not merely a bare
  isomorphism to some abstract set of the same cardinality.
- The original finite-local-freeness hypothesis supplies a trivializing
  pro-etale covering. Applying the assertion for every trivialization gives
  the final local-constancy clause, including covers with varying ranks.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtension`:
  `Padic.coefficientExtensionAbsoluteValue`, `Padic.coefficientExtensionIntegers`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`, imported by
  `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: the recorded small-site
  presentation `X.ProEt`, `Scheme.ProEt.topology X`.
- `Sheaf.CategoryTheory.RingedSiteModules`, imported by that inverse-image
  module: `CategoryTheory.ringedSiteModules` is exactly `SheafOfModules`;
  the latter is used directly with its actual linear isomorphisms.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`, imported publicly by
  that inverse-image module: `SheafOfModules.changeOfRings`,
  `changeOfRingsPresheaf`, `changeOfRingsHom`, with all three site/coefficient
  universes specified. The inclusion into the rationalization uses the actual
  module-sheafification unit of that presheaf.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`
  and its actual `toSheafify` unit.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.over`, `Over.map`; these implement the localized inverse
  image required in the node and agree sectionwise with the recorded general
  pro-etale inverse-image construction.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFree`; the full declaration/docstring was
  read, including its finite local generating families and varying rank.
- The stated proof-dependency modules are imported. The generic sheaf gluing,
  open-stabilizer, and local-sheafification lemmas remain proof obligations.
  `def-weil-pbc-site-comparison-morphism` currently has neither `lean` nor a
  Mathlib match, so there is no proof-dependency module to import for it.

Edge cases checked: n=0 uses empty finite sums and the one-element group GL_0;
zero rational/integral modules remain allowed. An empty scheme or empty test
object gives the unique section by the sheaf axiom. The image criterion also
identifies every zero pair there; no point is chosen in the statement. A
nonempty object is needed only in the node's proof of coset injectivity, with
its empty-object argument retained in the proof docstring. Disconnected
schemes and varying local ranks are allowed. The ring/module universe u+1
contains both small-site universes; isomorphism-class sections use u+2, with
matching lifts for the constant coset set. There is no independent smaller
universe for test schemes and no forced equality of site object/Hom universes.

Searches:

- `msearch.py leanfinder`, query “The sheaf of integral lattices in a finite
  locally free pro-etale p-adic sheaf is locally constant with fiber
  GL_n(E)/GL_n(O_E)”: eight hits, generic condensed/locally-constant-module
  functors and module-rank results. These concern other sites or algebraic
  ranks; none states the lattice-pair quotient and normalized coset map.
- `msearch.py loogle`, query `"Sheaf", "constant"`: twelve hits including
  `constantSheaf` and `Sheaf.IsConstant`. Read ConstantSheaf.lean: the former
  is used; none supplies the lattice theorem.
- `msearch.py grep`, query `IntegralLattice|latticeSheaf|lattice.*[Pp]resheaf`
  in AlgebraicGeometry: zero hits.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for
  `latticeSheaf|IntegralLatticePair|integralLatticeSheaf`: zero hits. Searching
  the upstream source for the exact node id also gave zero hits.
- Read the exact side-framework `CategoryTheory/RingObjects/ContinuousMap.lean`.
  Its `continuousMapRingSheaf` is RingCat-valued and restricts T to Type 0.
  It cannot feed the recorded CommRingCat change-of-rings API for E : Type u.
  The helper here keeps commutativity and the arbitrary coefficient universe,
  with the same explicit functions and maps; it is not an arbitrary coefficient
  object. The general fpqc continuous-function descent already exists in
  Mathlib/AlgebraicGeometry/Sites/ConstantSheaf.lean and is the proof input.
- `tools/blueprint_refs.py search 'lattice sheaf'`: zero blueprint-node matches;
  DAG searches found this statement and its downstream etale-lattice theorem,
  not a separate definition of its pair-class presheaf.
- `msearch.py leansearch`, query “Integral lattices in a locally free sheaf
  over continuous p-adic coefficients form a locally constant sheaf”: service
  unavailable, Internal Server Error. LeanFinder, Loogle and grep succeeded.

Read Bhatt--Scholze pp. 58--60 directly: Definition 6.8.1, Definition 6.8.3,
and Proposition 6.8.4(6) and its proof. The discussion explicitly starts with
an arbitrary scheme. No missing noetherian hypothesis was introduced.

Validation: the module passed `scompile.py` with no errors or warnings (only
postponed theorem proofs). All written variables and universes are explicit.
No new nodes or dependency-module replacements are needed; the helpers express
constructions already introduced within this item's own statement.

## Statement corrected

The old statement said “is the set of right cosets” while displaying
`S_n = GL_n(E)/GL_n(A)` and prescribing `g GL_n(A) ↦ g A_U^n`.
In standard group terminology, and in Mathlib, gH is a left coset; it is an
orbit for RIGHT multiplication. A quotient by the sets Hg would give the
wrong equivalence relation for this specified map. The correction replaces
only those words by “is the set of cosets g GL_n(A), namely the orbits for
right multiplication by GL_n(A).” For a concrete distinction, let g = diag(l,1) and let h be the integral
upper-unipotent matrix [[1,1],[0,1]]. The matrices g and hg are in the same
Hg coset, but hg A^2 contains (1,1), whereas g A^2 does not since l is a
nonunit. Thus the explicitly intended gH quotient must be retained.
Every formula, hypothesis and conclusion is unchanged. `statement_change.old_statement` preserves the full old text.

Source: Bhatt--Scholze, Proposition 6.8.4(6), proof, p. 60: the displayed
quotient and the explicitly prescribed map `g ↦ g O_E^n`.

Citer audit (all nodes whose stmt_deps or proof_deps name the item):

- `lem-weil-pbc-lisse-lattice-etale-local`: holds true. It uses local constancy
  of the same sheaf to descend a lattice to an etale cover. Clarifying the
  orbit convention preserves both the sheaf and its normalized model.

No unit statement is changed. No citer is edited. There is no unresolved
STATEMENT-DISPUTED flag.

## Second reading by NF

Independent review with the sandbox node, its Lean module, dependency nodes and
sources open. I first checked the corrected coset convention against
Bhatt--Scholze, Proposition 6.8.4(6), printed pp. 59--60, then matched the
formal statement. Section 6.8 begins on p. 58 with an arbitrary scheme;
the later topologically-noetherian restriction starts after Corollary 6.8.5
and does not apply here. Definition 6.8.1 supplies continuous coefficients,
and Definition 6.8.3 supplies the locally-free hypothesis.

Object/hypothesis/conclusion inventory and verdicts:

1. Prime ell and finite field extension E/Q_ell: `l`, `[Fact l.Prime]`,
   `E`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`.
   Exact. There is no extra ramification or characteristic hypothesis.
2. A with its induced topology, and E with its canonical topology:
   `latticeCoefficientIntegers l E` is the comap of the dependency's
   `Padic.coefficientExtensionIntegers` along `WithAbs.equiv`; the rational
   type is `WithAbs (Padic.coefficientExtensionAbsoluteValue l E)`.
   Exact transport of the recorded field and valuation subring. The
   subring topology is induced, rather than an extra assumed topology.
3. Arbitrary scheme and small pro-etale site: `X : Scheme.{u}`,
   `X.ProEt`, `Scheme.ProEt.topology X`. Exact. No quasi-compactness,
   quasi-separatedness, connectedness or noetherianity is assumed.
4. Coefficient ring sheaves: `latticeCoefficientPresheaf` has precisely
   lifted continuous functions, pointwise ring operations and precomposition.
   `latticeCoefficientSheaf` adds its sheaf-condition proof;
   `integralLatticeCoefficientMap` is induced by the actual subring inclusion.
   Exact, including the scalar map on localized sites `latticeScalarMap`.
5. L is a finite locally free rational module sheaf: the binder
   `L : SheafOfModules ... (latticeModuleRing ...)` and
   `[L.IsFiniteLocallyFree]`. Exact. I read upstream `LocallyFree.lean`:
   this predicate uses covering local generating families with isomorphism
   maps and finite index types, allowing varying ranks.
6. Pairs over each U: `IntegralLatticePair` has an integral module sheaf,
   `locallyFree : module.IsFiniteLocallyFree`, and the linear isomorphism
   `rationalization : changeOfRings ... module ≅ L.over U`.
   Exact. The tensor is sheafified sectionwise scalar extension, not an
   un-sheafified tensor or a scalar-extension existence assumption.
7. Identification of pairs: `IntegralLatticePair.Equivalent` says there
   exists an integral module isomorphism whose extended hom intertwines the
   two rationalizations, with the displayed composition in the correct order.
   Exact; no quotient by arbitrary rational automorphisms is introduced.
8. The pair-class presheaf is a sheaf of sets: the existential `F`, `c`
   and `IsLatticeClassPresentation` give sectionwise surjectivity and
   equality iff equivalence. These give precisely a bijection with the
   set of isomorphism classes on each U. The third clause identifies all
   restriction maps through `Over.map f` and equality of embedded images
   on all test objects. Exact: the map to a rationalization is
   `m ↦ α(1 ⊗ m)` through the actual sheafification unit. It is injective
   locally in a free integral basis, so pairs are equivalent exactly when
   these submodule images agree. Localization pulls back these images by
   restriction. Thus the clause expresses the specified inverse image,
   without assuming any arbitrary comparison map.
9. Every trivialization of rank n gives the constant model: the quantifiers
   are `∀ U n e, ∃ k`, after the single globally presented sheaf F.
   `latticeFreeSheaf` is the finite coproduct of the ring unit indexed by
   lifted `Fin n`, hence the correct rational free sheaf. Exact.
10. The model set is GL_n(E)/GL_n(A): `integralMatrixSubgroup` is the
    range of `Matrix.GeneralLinearGroup.map A.subtype`, and
    `integralMatrixCosets` uses Mathlib's subgroup quotient. I read
    `QuotientGroup.leftRel`: equivalence is `g⁻¹ * h ∈ H`, precisely gH
    cosets, with no normality premise. Exact for the corrected statement.
11. The constant sheaf is the sheafification of the discrete constant
    presheaf: the expression is `constantSheaf ... (Type (u + 2))`
    applied to the lifted coset type. I read its Mathlib definition as
    `Functor.const ⋙ presheafToSheaf`. Exact; this is not a ring of
    continuous functions into a topological quotient.
12. The specified isomorphism sends each constant gH to g A_U^n with
    its inclusion rationalization: the last iff identifies the image of
    the `toSheafify` constant section under k with `c U P` exactly when
    P's embedded image, in coordinates e, is `matrixLatticeImage ... g`.
    This helper is the explicit finite sum of columns of g with continuous
    integral coefficients. Exact normalization. Although written at the
    terminal slice object, naturality restricts these same constant
    sections to every test object; constants locally generate their
    sheafification, so this specifies the full canonical map.
13. Local constancy with varying ranks: the preceding assertion for every
    U, n, e applies on the covering provided by `IsFiniteLocallyFree`.
    Exact; no common global rank is silently imposed.

Dependencies were checked against their recorded signatures and definitions:
`CoefficientExtension.lean` for the field and its integers;
`ProEtaleDerivedCategory.lean` and Mathlib `Proetale.lean` for the site;
`RingedSiteModules.lean` (a transparent alias of `SheafOfModules`);
`TensorProduct.lean` for `changeOfRingsPresheaf`, `changeOfRings` and
`changeOfRingsHom`; `ProEtaleInverseImage.lean` for the canonical site
inverse-image interface; Mathlib `PushforwardContinuous.lean` for `over`
and `Over.map`; and Mathlib `ConstantSheaf.lean`. The change-of-rings
interface has independent site Hom, object and coefficient universes and
is instantiated here as `{u, u+1, u+1}`. Localized restriction uses the
existing Mathlib slice implementation, not a private inverse image.

Edge cases: `n = 0` has empty sums, the zero free sheaf and singleton
GL_0 quotient. Zero L and zero integral modules are permitted. Empty X
and empty test schemes use the empty-cover sheaf axiom; neither the
statement nor its normalization chooses a point. Empty covering/index
families are not ruled out. Disconnected X permits varying finite ranks.
Every prime, including 2, is allowed. The site retains object universe
u+1 and Hom universe u; module sections are in u+1 and the pair-class
presentation is allowed in u+2. All universes and variables are explicitly
bound; no independent smaller test-scheme universe makes a clause vacuous.

Independent searches with different wording:

- LeanFinder: "Integral locally free submodule sheaves of a continuous
  p-adic vector bundle are classified locally by an open general linear
  subgroup quotient". Eight returned types concern Nobeling freeness,
  algebraic free loci, condensed modules and free-sheaf hom equivalences.
  None states this pair-class sheaf or its normalized quotient model.
- Loogle: `"GeneralLinearGroup", "quotient"`. One hit is a subgroup
  quotient action in modular forms over real GL_2; not this statement.
- msearch grep: `lisse.*lattice|lattice.*[Ss]heaf|GL.*[Cc]oset`.
  Five hits are complete-lattice instances for ideal sheaves, unrelated.
- Direct rg in Mathlib AlgebraicGeometry/Sites, upstream ConstructibleSheaf,
  upstream and side-framework SixFunctors/ProEtale, side
  ConstructibleSheaf/ProEtaleModule, and project Sheaf/Paper. Hits concern
  the older rationalized-lattice category, stable representation lattices,
  or documentation; none gives this theorem or pair-class construction.
- I read the exact side-framework `RingObjects/ContinuousMap.lean`:
  `continuousMapRingPresheaf` and `continuousMapRingSheaf` require T : Type 0
  and take values in RingCat. This does not supply the commutative coefficient
  sheaf in arbitrary Type u needed by the recorded tensor interface. The
  helpers retain its continuous functions and precomposition, generalizing
  only coefficient size and commutative-ring packaging. Mathlib's
  `isSheaf_fpqcTopology_continuousMapPresheaf` has arbitrary target universe
  and supplies the existing descent input described in the proof docstring.

No new nodes or dependency modules were delivered by the first worker;
there are none requiring an additional stage-1 or dependency-module review.
All helper definitions contain specified data. The only new postponed
proofs are the named coefficient sheaf-condition theorem (the proof
component of the explicit coefficient construction in this node) and the
main lattice theorem. Both have source/blueprint docstrings and complete
proof plans. The main docstring follows all seven DAG proof steps. No
proof was filled, and no definition data is a sorry or an unconstrained
existence choice.

Correction/citer audit: I agree with the recorded source-based clarification
from "right cosets" to gH/right-multiplication orbits. The old statement is
preserved in `statement_change.old_statement`; the displayed source map
is g ↦ g O_E^n. An exhaustive search finds exactly one external citer,
`lem-weil-pbc-lisse-lattice-etale-local`; I opened its statement and all
three proof steps. Its `holds: true` verdict is correct: it uses precisely
local constancy and the identity-coset lattice on each trivializing object.
There is no second external citer to open, and no unit statement changes.

Mismatch repaired in this reading: DAG proof step 4 retained the words
"The right cosets are equal" after the statement correction. Replaced
that sentence by "The cosets g GL_n(A) are equal", consistently with the
existing correction. The Lean objects, signature and data were already
correct and were left unchanged. No remaining mathematical mismatch or
STATEMENT-DISPUTED flag was found.

Validation of the second reading: `scompile.py NF
lem-weil-pbc-lattice-sheaf-locally-constant <absolute module path>`
compiled both its sandbox probe (6.8 s) and library module (7.1 s),
with no errors or warnings. A literal comparison of the source signature
before `:= by` with `lean.statement` passed without normalization.
