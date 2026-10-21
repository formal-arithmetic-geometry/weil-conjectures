## Worker report

The module `Sheaf.CategoryTheory.RingedDerivedPullbackLinear` supplies the real construction
`SheafOfModules.scalarSectionLinear` and states
`SheafOfModules.ringedDerivedPullback_linear`. Only the theorem proof is postponed (`sorry`).
The item node changes only in `lean`; there is no statement correction, new node, or dependency repair.

Hypotheses and clauses, matched to the node:

- A commutative unital scalar ring is `(R : Type v) [CommRing R]`. Its universe is independent
  of the coefficient/module universe. No field, nonzero-ring, or characteristic assumption occurs.
- Small presented sites are `{C D : Type u} [SmallCategory C] [SmallCategory D]` and `JC,JD`.
  The ring sheaves `A,B : Sheaf ... CommRingCat.{u}` explicitly retain commutativity and units.
  `ringedSiteModules.{u,u,u,u}` is the recorded module category and uses the module universe
  bounding these sites. `HasDerivedCategory.{w}` states the recorded localization size convention.
- The ringed-topos morphism is `u : RingedToposMorphism B_ring A_ring`. Its reversed order is
  deliberate: `u.inverse` goes from sheaves on C to sheaves on D, and `u.ringMap` goes from
  inverse image of A to B. Its adjunction and finite-limit preservation are structure fields;
  no functor of presented sites is assumed.
- `AI,I,c,hstruct` present precisely the structural map in the recorded algebraic inverse-image
  language: `I` transports A and its modules, `c : AI ⟶ B`, and `hstruct` identifies their
  composite with `u.ringMap`. The small-site `AlgebraicInverseImage` specialization is retained
  by the recorded `AlgebraicInverseImageOfUniverses` module. It is usable here without forcing
  unequal site universes together: the item explicitly uses sites small in the module universe.
- The unital homomorphisms to global sections are `sA,sB : R →+* RingCat.sectionsSubring ...`.
  This subring is literally all section families compatible with every restriction, rather than
  evaluation at an assumed final site object.
- `hs` is exactly scalar compatibility through the structural map. For each `r`, every
  generalized constant section `a : T ⟶ |A|` with value `(sA r).val U` is sent by inverse image
  followed by `u.ringMap` to the constant section `(sB r).val V`. This is equivalent to the
  global-section equation: take T terminal for one direction; pull back that terminal section
  along the unique T-to-terminal map for the other. Left exactness supplies the terminal
  identification. It neither assumes generation by global sections nor a terminal site object.
- `scalarSectionLinear R A sA` and its B counterpart give actual structures, by restricting the
  existing `homLinear` Hom modules along `sA,sB` using `Module.compHom`. Thus their scalar action
  is `(r • f).val.app U x = (sA r).val U • f.val.app U x` (and likewise for B), with the existing
  addition. The two instance lambdas in the conclusion are immediately applied to these real
  constructions, not arbitrary existential linear structures. Mathlib induces the derived
  structures from these, as specified by `lem-weil-linear-abelian-derived-category`.
- `uStar,hobj,hmap` specify exactly the ordinary tensor pullback of the recorded dependency:
  extension of scalars of `I.modules` on objects AND morphisms. Its additive instance is part
  of this standard presentation, not exactness of pullback; no flatness of c is assumed.
- `LF,epsilon` and `LF.IsLeftDerivedFunctor epsilon ...` specify the canonical derived
  pullback by its universal property, exactly the first two witnesses and first property of
  `ringedTopoiDerivedPullback`. This applies to its actual K-flat construction. Quantifying
  over its realizations adds no substantive hypothesis or stronger geometric conclusion:
  uniqueness gives the canonical natural isomorphism of any such realization with it.
  The proof docstring explains transporting the K-flat comparison along that isomorphism.
- `LF.Additive ∧ Functor.Linear R LF` is the node's R-linearity on all derived Hom modules.
  The final universally quantified equality `LF.map (r • 𝟙 X) = r • 𝟙 (LF.obj X)` states its
  particular scalar-endomorphism assertion, using the specified actual scalar-section action
  and the induced localization structure. There is no boundedness, torsion, completeness,
  constructibility, or flatness condition.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedToposMorphism`: `CategoryTheory.RingedToposMorphism`, including
  the geometric adjunction, left exactness, structural map, and induced module direct image.
- `Sheaf.Paper.RingedTopoiTensorSections`: `SheafOfModules.RingedTensor.ringSheaf`,
  the existing abbreviation for the underlying ring sheaf of a commutative ring sheaf.
  Using it prevents repeated expensive elaboration of sheaf-composition instance terms.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the transparent
  abbreviation of `SheafOfModules`; the existing `SheafOfModules.instAbelian` is used, not chosen.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Qh`, and its localization of the homotopy category at quasi-isomorphisms.
- `Mathlib.CategoryTheory.Linear.Basic`: `CategoryTheory.Linear` and its bilinear composition.
- `Mathlib.Algebra.Homology.DerivedCategory.Linear`: `DerivedCategory.instLinear`, linearity
  of Q/Qh, and linearity of shifts. These supply exactly the induced derived actions.
- `Mathlib.CategoryTheory.Linear.LinearFunctor`: `CategoryTheory.Functor.Linear` and the
  additive-functor convention; its scalar-identity characterization also matches the proof.
- `Sheaf.Paper.RingedTopoiDerivedPullback`: `SheafOfModules.ringedTopoiDerivedPullback`.
  Its full existential signature, natural epsilon, universal property, exactness, K-flat
  comparison, and resolution naturality/composition clauses were read. It is imported for
  the proof, together with the recorded tensor and K-flat-resolution modules.
- `Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses` publicly retains
  `SheafOfModules.AlgebraicInverseImage`; its full generalized ring/module operation graph
  conditions and natural underlying-module identification were read and used for the
  small-site specialization in this statement.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the recorded monoidal
  localization structure and retained tensor constructions, proof import.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`, including K-flatness,
  term flatness, quasi-isomorphism and degreewise epimorphism, proof import.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated` and `.Functor`: recorded triangulated
  category and exact-functor conventions, available through the derived category imports.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule`: `homModule,homLinear` supply
  the existing global-section action; no second copy was constructed.

Edge cases checked mathematically: R zero and coefficient zero rings; r=0 and r=1; empty
sites (all section families have their correct degenerate meanings); zero complexes and zero
objects; the identity ringed morphism; a point with the nonflat map Z→Z/2. The last example
has tensor balancing and a left-derived pullback, even though ordinary pullback is not exact.
No finite/bounded complex assumption or global-generators assumption was introduced.

Searches for existing declarations (2026-10-21):

- `msearch.py ... leanfinder "Derived pullback between ringed topoi is linear over compatible
  global scalar sections without flatness"`: eight hits, including ordinary
  `SheafOfModules.pullback`, pullback composition/isomorphism and scheme pullback; none state
  the arbitrary-geometric-morphism unbounded K-flat scalar theorem.
- `msearch.py ... loogle "CategoryTheory.Functor.Linear, CategoryTheory.Functor.IsLeftDerivedFunctor"`:
  zero hits.
- `msearch.py ... grep "Linear|linear" CategoryTheory/Triangulated/DerivedFunctor`: zero hits.
- `msearch.py ... leansearch "The K-flat left derived pullback of sheaves of modules preserves
  compatible scalar sections and is linear"`: eight hits; ordinary module pullback and
  `Functor.instLinearDerivedCategoryMapDerivedCategory` (the exact-functor derived map).
  The latter assumes ordinary exactness and cannot handle the nonflat ring-map case here.
- `msearch.py ... grep "sectionsSubring|homLinear" Algebra/Category/ModuleCat/Sheaf`: zero hits.
- Local `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for scalar/linear ringed pullback,
  `centralScalar`, `scalarSection`, and proposed declaration names; and `grep -rn` for the
  item id in `lean/WeilConjectures`: no exact theorem. Found and read the existing HomModule
  action and the pro-etale ordinary-operation specialization
  `proEtaleRingDerivedOperations_scalarLinearity`. That specialization requires identified
  coefficient rings and an exact ordinary pullback; it is not this arbitrary-c theorem.
  Reused HomModule rather than duplicating its sectionwise structure.

Read the local Stacks proof of Tag 06YY (sites-cohomology.tex, lemma-derived-base-change),
the pullback definition in Tag 03D6, and conventions.tex section-algebra. The module docstring
carries all five proof steps of the node, including naturality, resolution conjugation,
and deduction of full linearity from scalar identities. No statement dispute was found.

## Second reading by NU

A separate pass by the same worker reopened the node and final module. The dispatcher
explicitly prohibits starting another agent; this paragraph does not claim an independent
review. Independent maintainer review remains the delivery's next stage.

The pass checked the direction of `RingedToposMorphism B_ring A_ring`, the equality tying c
back to its actual structural map, both global-section homomorphisms, the generalized
constant-section compatibility equation, actual sectionwise scalar actions, the induced
ordinary unbounded derived categories, and the additive/linear/scalar-identity conclusions.
In particular, LF is fixed by a universal derived property, rather than merely by an
objectwise isomorphism on some representatives. Tensor pullback is fixed on maps as well
as objects. No flatness was added. Compiler-guided repairs supplied the standard filtered-
colimit instance import for small-site module sheafification explicit universe arguments
for the scalar helper and derived categories, and reuse of the existing `ringSheaf`
abbreviation to avoid repeatedly elaborating large sheaf-composition instance terms. The scalar ring universe remains independent.

## Validation

Every compile uses the prescribed `scompile.py` wrapper. Final compile and delivery preflight
results are recorded below after the required checks complete.

Final `scompile.py` check passed cleanly with no warnings: sandbox 32.3 s, final module
35.0 s. No timeout setting or heartbeat limit was increased. The profiler was confined
to nondelivered scratch probes; the final module contains no tracing or profiling options.

`deliver2.py NU lem-pur-ringed-derived-pullback-linear --no-push` passed: the tool printed
`OK (dry run): commit 1b221698727 passes the preflight and compiles; nothing pushed`.
The staged packet consists exactly of the item node, its module, and this report.
