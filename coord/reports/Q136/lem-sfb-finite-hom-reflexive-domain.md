## Worker report

The module `Sheaf.RingTheory.FiniteHomReflexiveDomain` states
`Module.isReflexive_linearMap_of_finite_of_isNoetherianRing`, with proof `sorry`.
It introduces no definitions, instances, extra hypotheses, or auxiliary theorems.
Only the item's `lean` field changes. No statement correction or dispute is needed.

I read Stacks `literature/stacks-project/more-algebra.tex`,
`lemma-dual-reflexive` (Tag 0AV3), including its finite-presentation proof.
It assumes a Noetherian domain, finite M, and finite reflexive N, and concludes
reflexivity of Hom(M,N), exactly as the node and Lean declaration do.

Clause and hypothesis correspondence:

- The commutative ring R is `{R : Type u} [CommRing R]`.
- Noetherianity is `[IsNoetherianRing R]`, the recorded declaration of
  `def-weil-pbc-noetherian-ring`; this says that every ideal is finitely generated.
- Integral-domain status is `[IsDomain R]`; in particular, the zero ring is excluded
  exactly as by the source's word "domain".
- The modules M and N are independently quantified by `{M : Type v}` and
  `{N : Type w}`, with `[AddCommGroup M] [Module R M]` and their counterparts for N.
- Their finite generation is `[Module.Finite R M] [Module.Finite R N]`, using
  `def-weil-finitely-generated-module`'s existing Mathlib declaration.
- The node's T* is `Module.Dual R T`, defined as `T →ₗ[R] R` in
  `Mathlib.LinearAlgebra.Dual.Defs`, lines 60–63.
- The evaluation map is that file's `Module.Dual.eval R T`, defined by
  `LinearMap.flip LinearMap.id` at lines 78–85. Its `eval_apply` equation is
  `Module.Dual.eval R T t λ = λ t`, exactly the node's formula.
- Reflexivity of N is `[Module.IsReflexive R N]`. This class, lines 212–218,
  asserts bijectivity of the specified evaluation linear map. This is equivalent
  to that map being an R-linear isomorphism: `Module.evalEquiv` at lines 228–234
  bundles precisely this map, and its inverse is linear. It is not an arbitrary
  equivalence to the bidual.
- The conclusion is `Module.IsReflexive R (M →ₗ[R] N)`.
- The Hom module uses Mathlib's canonical `LinearMap.module` instance, not a
  separately supplied module structure. `LinearMap.add_apply` and
  `LinearMap.smul_apply` in `Mathlib.Algebra.Module.LinearMap.Defs`, lines 835
  and 751 respectively, give exactly the pointwise operations in the node.
- Universes `u v w` are declared explicitly and remain independent. The Hom type
  and its duals use the resulting maximum universes. No implicit variables or
  same-universe restriction are introduced.

Dependency declarations read and used:

- Statement dependency `def-weil-pbc-noetherian-ring`:
  `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`; the abbreviation and
  `isNoetherianRing_iff_ideal_fg` were read at lines 192–210.
- Statement dependency `def-weil-finitely-generated-module`:
  `Mathlib.RingTheory.Finiteness.Defs`, `Module.Finite`; the docstring and
  `fg_top` field were read at lines 116–129. Its finite-ring and field clauses
  are explanatory specializations, not additional hypotheses here.
- Reflexivity and duals use the existing Mathlib definitions above; the node
  itself gives this terminology, so no missing notion requires a new node.
- Proof dependencies `lem-sc-noetherian-finite-module-finite-presentation` and
  `def-sc-finitely-presented-module`: plain import
  `Mathlib.Algebra.Module.FinitePresentation`, using
  `Module.finitePresentation_of_finite`, `Module.FinitePresentation`, and
  `Module.FinitePresentation.exists_fin'`; full signatures were read at
  lines 60–125.
- Proof dependency `lem-weil-pbc-noetherian-submodule-finite`: plain import
  `Mathlib.RingTheory.Noetherian.Basic`, `Submodule.FG.of_le`; its signature
  and docstring were read at lines 375–385. Applying it below the finite top
  submodule is the recorded one-line specialization.
- Proof dependency `lem-per-finite-injection-bidual-injective`: plain import
  `Sheaf.RingTheory.FiniteInjectionBidualInjective`,
  `LinearMap.dualMap_dualMap_injective_of_injective_of_finite`.
  I read its whole module, including the proof docstring and explicit
  independent universes, finite-module hypotheses, and injectivity conclusion.

The theorem docstring carries all four DAG proof steps: finite presentation and
the coordinate maps, finite-power reflexivity, identification of the Hom kernel
and its finiteness, and the bidual injection/evaluation diagram chase. Imports
used only by that proof plan are plain imports, as required by stage 2.

Edge cases checked before writing:

- M = 0 or N = 0 gives the zero Hom module; its evaluation is the unique
  isomorphism between zero modules. Neither is excluded by the signature.
- M = R gives Hom(R,N) identified by evaluation at 1 with N, agreeing with the
  assumed reflexivity of N.
- M = Z/2 and N = Z over R = Z gives zero Hom. No torsion-freeness or projectivity
  hypothesis is imposed on M.
- Empty finite powers in the proof plan are zero modules, so both n = 0 and
  m = 0 remain valid.
- Fields in any characteristic are included; no characteristic assumption or
  positive-rank assumption occurs.

Searches actually run with `msearch.py Q136 lem-sfb-finite-hom-reflexive-domain`:

- `leanfinder`: "Over a Noetherian integral domain Hom from a finite module into a
  finite reflexive module is reflexive". Eight hits: finite-free/projective
  reflexivity, finite Hom in FGModuleCat over a field, reflexivity itself,
  split summands, and related field results. None gives the item.
- `loogle`: `Module.IsReflexive, LinearMap`. Twelve hits, including
  `Module.IsReflexive.of_split`, the evaluation lemmas, and field annihilator
  results. None asserts general finite Hom reflexivity over a Noetherian domain.
- `grep`: `IsReflexive|reflexive` in `LinearAlgebra/Dual`. Ten hits in Defs and
  Lemmas. I read the actual class and the dual instance: that instance assumes
  the original module reflexive, so it does not cover arbitrary finite M here.
- `leansearch`: "Hom of a finite module into a finite reflexive module over a
  Noetherian integral domain is reflexive". Eight hits, including perfect-pairing
  consequences, the dual instance, and finite projective reflexivity; no exact match.
- `rg -n 'IsReflexive|finite.hom.reflexive|dual-reflexive'` in both project Lean
  trees found finite-product reflexivity upstream, cyclic DVR quotient duality,
  saturated embeddings, flat base change, and height-one criteria, but no Hom
  theorem. `grep -rn 'lem-sfb-finite-hom-reflexive-domain'` in WeilConjectures
  returned no match.
- The final proposed name
  `isReflexive_linearMap_of_finite_of_isNoetherianRing` was searched in Mathlib,
  WeilConjectures, Sheaf, and `dag/lean_names_upstream.json`: no match.

Validation: the module is compiled with the prescribed `scompile.py` server
wrapper; dry-run and delivery use the prescribed `deliver2.py` wrapper.
Only the expected theorem proof is postponed.

## Second reading by Q136

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
