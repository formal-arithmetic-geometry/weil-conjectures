## Worker report

The module `Sheaf.AlgebraicGeometry.NoetherianAffineFreePresentation` states
`AlgebraicGeometry.Scheme.exists_noetherian_affine_free_presentation`, with its sole proof
`sorry`. It defines two concrete helper abbreviations by real categorical constructions:
`affineFreeEtaleModule` is the recorded étale sum-extension applied to the constant regular
module; `finiteAffineFreeCoproduct` is its finite coproduct, with the finite-coproduct
instance explicitly selected. They introduce no alternative sheaf category, stratification,
local-constancy predicate, or extension-by-zero construction.

### Each hypothesis and conclusion

* A scheme X: `(X : Scheme.{u})`, the recorded `AlgebraicGeometry.Scheme`.
* Quasi-compact and quasi-separated X: `[CompactSpace X] [QuasiSeparatedSpace X]`, the
  usual equivalent underlying-space versions of the scheme conventions.
* A commutative Noetherian ring: `(R : Type (u + 1)) [CommRing R] [IsNoetherianRing R]`.
  There is no `Finite R`, `Fintype R`, nonzero, characteristic, base-field, or Noetherian-X
  hypothesis. The coefficient universe follows the recorded small-étale ModuleCat convention.
* An R_X-module sheaf on the small étale site:
  `(F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))`. This is the established
  constant-coefficient encoding, explicitly exposed by the local-finite-type dependency's
  repaired record. Sectionwise R-linearity extends uniquely to the locally constant ring
  coefficients; the sheaf condition glues the locally constant scalar action. Thus this
  encoding describes modules over the constant ring sheaf, with their linear maps.
* Constructibility: `[IsConstructibleSheaf F]` from
  `WeilConjectures.ConstructibleSheaf.Defs`. I read its full definition and its constituent
  definitions. It existentially chooses `Scheme.Stratification X`: a finite disjoint
  locally closed partition with scheme immersions and constructible strata
  (`Topology.Stratification.isConstructible_stratum`). Each inverse-image restriction via
  `Etale.upperStar` is `IsFiniteLocallyConstantSheaf`, i.e. étale locally constant with
  finitely generated geometric stalks. For ModuleCat finite generation means
  `Module.Finite R`, not finiteness of the underlying set. Local constant charts and their
  finitely generated stalks give exactly local constant finitely generated values; around
  a point of a constant chart use its stalk identification to obtain that finite value,
  shrinking to its nonempty covering members when necessary. Empty members impose no
  extra condition. This is the specialization exposed in the recorded
  `def-weil-pbc-locally-constant-finite-type-modules` interface.
  The separate `FiniteLocallyClosedStratification` declaration is imported from the recorded
  dependency; the upstream stronger stratification bundles exactly the constructible-strata
  clause that this item adds to that dependency. No extra restriction is imposed.
* Finite families: `∃ (n m : ℕ) (U : Fin n → X.Etale) (V : Fin m → X.Etale)`.
  `X.Etale` carries precisely the étale structure morphisms to X.
* Affineness: `(∀ i : Fin n, IsAffine (U i).left)` and the identical V condition.
* Each summand is literally
  `(Etale.etaleLowerShriek (ModuleCat R) W.hom inferInstance).obj
  ((constantSheaf W.left.smallEtaleTopology (ModuleCat R)).obj (ModuleCat.of R R))`.
  This is j_W! R_W, using the dependency's sheafified sum-extension, including the
  regular R-module rather than an arbitrarily chosen module or a free-generator axiom.
* The two sums are `finiteAffineFreeCoproduct X R m V` and
  `finiteAffineFreeCoproduct X R n U`. They are the colimits of the associated discrete
  finite diagrams, hence the indicated direct sums. The helper only fixes the instance
  selection to prevent repeated expensive general-colimit inference.
* Exact sequence ending F → 0: the quantified `f`, `g`, and `(w : f ≫ g = 0)` together
  with `Nonempty (IsColimit (CokernelCofork.ofπ g w))` assert that g is the cokernel of f.
  In the abelian sheaf category this is equivalent to exactness at the middle term and
  epimorphy of g. No injectivity at the first term is requested or added.
* Both m,n may be zero: the natural-number quantifiers are unrestricted. The finite
  coproduct includes its empty (zero-object) case.
* Infinite coefficient rings and infinite underlying module sets remain allowed.
* Constructibility of the strata is explicitly built into the reused upstream
  stratification; it is automatic on Noetherian X, as its documented
  `IsConstructibleSheaf.of_noetherianSpace` records. The theorem does not require X
  Noetherian.

### Dependency declarations read and used

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme Hom.
* `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` = every ideal finitely generated.
* `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`, the
  sheafification of the constant presheaf.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  transparent general-site `SheafOfModules` encoding. The fixed-coefficient ModuleCat
  presentation above is the established étale specialization, not a second category.
* `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`, on `Scheme.Etale`.
* `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification`, finite locally closed immersed partitions.
* `Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules`:
  `SheafOfModules.IsLocallyConstantFiniteTypeModules` and its public upstream
  `Scheme.IsFiniteLocallyConstantSheaf`, `Scheme.IsConstructibleSheaf` interfaces.
* `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite` (finite generation).
* `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`:
  `AlgebraicGeometry.Etale.etaleLowerShriek`, whose full signature and docstring define
  the sheafified sum-extension, not an arbitrary left adjoint.
* `def-weil-pbc-scheme-conventions` is a convention record with no declaration.
* `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
* `Mathlib.Topology.Constructible`: `Topology.IsConstructible`, Boolean algebra generated
  by retrocompact opens, so no replacement by a finite union of arbitrary locally closed
  subsets occurs.

Proof-only recorded modules are imported non-publicly. Unstated proof prerequisites are
not asserted as new theorems in this delivery; the proof docstring retains all seven
steps and all the node's proof inputs. Mathlib proof leaves are imported directly.

### Edge cases and source check

I opened the source Tag 095N in `literature/stacks-project/etale-cohomology.tex`,
lines 12412–12466: it explicitly permits affine U_i,V_j and identifies the presented
objects as cokernels. This item states its forward direction only, exactly as the DAG.
For F = 0, both index families can be empty; for empty X the same holds. For the zero ring
all coefficient sheaves are zero and no nontriviality assumption is needed. `R = ℤ` and
infinite finitely generated module values are allowed. There is no finite-set hypothesis.
The first map need not be monic; the cokernel formulation correctly avoids that claim.
No statement correction or statement dispute is needed.

### Searches for existing declarations

* `msearch.py leansearch`, query “A constructible sheaf of modules over a Noetherian ring
  has a finite presentation by extensions by zero from affine etale schemes”: eight
  hits on local quasicoherent presentations and scheme-structure module sheaves; no
  theorem giving these affine étale global generators.

* `msearch.py leanfinder`, query “A constructible etale module sheaf over a Noetherian ring
  on a qcqs scheme admits a finite affine free presentation”: eight hits, mainly
  `SheafOfModules.isFinitePresentation` and quasicoherent local presentation interfaces.
  These assert local finite rank presentations and do not give the claimed global
  finite families of affine étale sum-extensions.
* `msearch.py loogle`, query
  `SheafOfModules.IsFinitePresentation, CategoryTheory.Sheaf.freeYoneda`: zero hits.
* `msearch.py grep`, query `affine.*free.*presentation|constructible.*presentation`
  in `Algebra/Category/ModuleCat`: zero hits.
* `rg` on upstream `WeilConjectures` and `lean/Sheaf` for the item id and the proposed
  declaration/helper names found no competing declaration. A consumer docstring names
  this DAG item, but does not state its conclusion.
* Broader project searches found
  `Scheme.exists_affine_free_etale_presentation_general` in
  `Sheaf.AlgebraicGeometry.ConstructibleAffineFreePresentationGeneral`. I opened its
  full signature and proof. Its generators are sheafified free representables;
  its conclusion is not literally the sum-extension expression required here. The proof
  plan's step 2 is precisely the comparison needed between those representations, so
  this delivery states the required j_! regular-module formulation without redefining
  either construction. The existing finite-ring-only `IsConstructibleEtaleModuleSheaf`
  is deliberately not used, since it would exclude infinite Noetherian rings.

### Validation

Every binder and universe is explicit, with `set_option autoImplicit false`.
All definitions have real data and the only theorem proof is `sorry`.
The initial repeated coproduct expressions produced a typeclass timeout; the concrete
finite-coproduct helper selects `HasFiniteCoproducts.out` directly and compiled within
four seconds per file. The compiler wrapper checks both the sandbox module and its
actual library module name. Final compilation passed for both module names (5.3 s and 4.1 s). The prescribed
`deliver2.py --no-push` dry run passed preflight and compilation at commit `6011ad25a9`;
only this report search log was subsequently completed and the dry run is repeated.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
