## Worker report

The module `Sheaf.Algebra.Homology.SignedDoubleHomCone` states the signed double internal-Hom
comparison. It uses the existing `CategoryTheory.homComplex` and its projection interface,
then defines the ringed-site module category, integer cochain complexes, the contravariant
Hom functor `dual`, its double application `doubleDual`, component projections, the two
inclusions into the Hom of a cone, the one-step reindexing map, and the cone map of a
commutative square. The theorem `comparison` has proof `sorry` and packages exactly the
existence of the shift isomorphisms `s`, the shift comparison `chi`, and the cone comparison
`theta`, followed by all required component formulas and arrow identities.

The node's hypotheses render as follows. “Small site and commutative ring sheaf” is
`{C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
[J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})] {R : Sheaf J CommRingCat.{r}}`.
The module category is the existing `ringedSiteModules` abbreviation, and `Complex R` is
`CochainComplex (Modules R) ℤ`; thus every complex `A`, `B`, and `I` is an integer-indexed
cochain complex of sheaves of modules. `dual I` is the recorded Hom-complex bifunctor with
`I` fixed as target, and `doubleDual I` is its right-opposite composite.

The first conclusion clause, existence of `s K m`, is rendered by
`homComplex (K⟦m⟧) I ≅ (homComplex K I)⟦-m⟧`; its displayed projection equation uses
`(m * q).negOnePow` and the canonical shift component isomorphism. The second clause
exists `chi K : doubleDual I (K⟦1⟧) ≅ doubleDual I K⟦1⟧`, with its defining composite
and the local formula `(p + t).negOnePow`. The third clause exists `theta f` from the
double Hom of `mappingCone f` to the mapping cone of `doubleDual I.map f`; its two
component equations are rendered using `inB` and `inA`, with the sign
`(p + t).negOnePow`. The fourth clause quantifies a morphism of arrows `h : a ⟶ b` and
states naturality via `coneMap`; the fifth states compatibility with `mappingCone.inr`.
The final clause uses the standard cone triangle's third morphism and states the required
compatibility with `chi`. No boundedness, flatness, K-injectivity, exactness, or nonzero
assumption is added.

Dependencies used: `Sheaf.Algebra.Homology.HomComplexProjections`, declaration
`CategoryTheory.homComplex_projections_exists`; `Sheaf.Algebra.Homology.HomComplex`,
declaration `CategoryTheory.homComplex`; `Sheaf.CategoryTheory.RingedSiteModules`,
declaration `CategoryTheory.ringedSiteModules`; `Mathlib.Algebra.Homology.HomologicalComplex`,
declaration `CochainComplex`; and `Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated`,
declarations `CochainComplex.mappingCone`, `CochainComplex.mappingCone.map`,
`CochainComplex.mappingCone.inr`, `CochainComplex.mappingCone.triangle`, and
`CochainComplex.shiftFunctorObjXIso`.

Edge cases checked: `f = 0`, `f = 𝟙`, zero complexes, negative shifts and `m = 0`,
empty sites, arbitrary unbounded complexes, and characteristic two. The formulas use only
binary biproducts, products, reindexing and signs, so these cases remain included.

Searches made: `msearch.py ... leanfinder` for “Double internal Hom complex carries mapping
cones to mapping cones with signed shift comparison” returned only generic mapping-cone
and bifunctor-flip declarations; no exact result. `msearch.py ... loogle`
`CochainComplex.mappingCone.mapHomologicalComplexIso` returned the generic additive-functor
comparison, which is not this double internal-Hom statement. `msearch.py ... leansearch`
for “The double internal Hom complex preserves cones with Koszul signs” returned generic
bifunctor-flip and mapping-cone results only. `msearch.py ... grep` for
`doubleHom|double_hom|homComplex.*[Cc]one|[Cc]one.*homComplex` found no duplicate in
Mathlib or the source project. `rg` over `lean/Sheaf` found the covariant Hom-complex
mapping-cone interfaces but no double-Hom cone comparison. The exact source passages were
read in `sites-cohomology.tex` Section 0A8X, Lemma 08JC, and `derived.tex` Definition 014E.

No `STATEMENT-DISPUTED` flag or node fault.

Representation details: all four universes `u`, `v`, `w`, and `r` are explicit and
independent. Module carriers use `max u v w`, so the site is small relative to
the module universe and applying Hom twice stays in that universe. No equality
between object and morphism universes is imposed. `HasSheafCompose` is exactly
the structural instance required by the recorded Hom-complex interface to view
the commutative-ring sheaf as a ring sheaf; it is not a condition on the complexes.
The precoverage interface of `def-weil-pbc-sites-and-cohomology` is imported;
only its associated Grothendieck-topology/sheaf component is needed here.
The recorded abstract-derived-category module is imported as required, while
the comparisons themselves live before localization and require no localization.

`proj` and `productLimit` expose the already specified projections and their
product universal property from `homComplex_projections_exists`, rather than
introducing another internal Hom. The dependency
`lem-sc-hom-complex-projections` is added to `stmt_deps` because these helpers
use its already landed interface. There are no new nodes, dependency repairs,
or changes to the natural-language statement. The auxiliary declarations all
belong to the owning comparison node and are listed in `lean.declarations`.
Their data are real constructions. The only postponed proof in the delivery is
`CategoryTheory.SignedDoubleHomCone.comparison`.

The component equations are equations of sheaf morphisms (not global-section-only
conditions). For `theta`, restricting the outer Hom to `inB I f q` extracts
`alpha_q`, and restricting it to `inA I f t` extracts `beta_t`. The target cone's
`sndX` extracts alpha, and `fstX` extracts gamma. Mathlib stores the summands
in the order A[1], B, whereas the node writes B, A[1]; this changes only their
order, not the differential or either inclusion/projection. In particular
`(mappingCone.triangle f).mor₃` is **negative** projection, as verified from its
source definition. Thus the final conjunction is exactly
`chi_A ∘ T²(-pi) = -pi ∘ theta`, in Lean's left-to-right composition order.

A further self-check matched all nine conjunctions against the node: the sign
formula for s, its naturality, the defining composite for chi, its sign formula,
both components of theta, theta naturality, the inclusion identity, and the
negative-projection identity. Chi naturality follows from its defining composite
and the explicitly stated naturality of s. No extra mathematical assumption or
clause was introduced. The maintainer supplies the independent review under the
current direct-delivery workflow.

Validation: the full file compiled cleanly through `scompile.py` in both its
sandbox and library-module passes, most recently 16.1 s and 16.5 s respectively,
within the unchanged 60-second limit. No diagnostic probe or option remains.

## Second reading by Q123

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
