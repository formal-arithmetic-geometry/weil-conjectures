## Worker report

Item: lem-sfb-localized-affine-residue-criterion-quasifinite. Module:
`Sheaf.AlgebraicGeometry.LocalizedAffineResidueCriterion`. Main declaration:
`AlgebraicGeometry.localizedAffineResidueCriterion`. Its whole proof is `sorry`.
All four helper declarations have real data: two abbreviations for the displayed
coordinate rings and two canonical scalar-action instances. They belong to this
node's coordinate presentation and are listed in `lean.declarations`.
No new independent notion, dependency repair, or statement correction is needed.

Source read: `literature/stacks-project/varieties.tex`, Tag 0AB6,
`lemma-quasi-finite-in-codim-1`, especially its final paragraph. The node isolates
the fibre argument after transcendence degree zero is established; the dimension
and Noetherian assumptions used earlier in 0AB6 are therefore not hypotheses here.
The current blueprint unit `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`
was also read. The theorem docstring reproduces all seven steps of the node's
proof, including the affine description of the residue-field morphism added at
stage-1 review.

Hypotheses and objects, clause by clause:

| Node | Lean rendering |
| --- | --- |
| Schemes Z,S and g:Z→S locally of finite type | `(Z S : Scheme.{u}) (g : Z ⟶ S) [LocallyOfFiniteType g]` |
| V=Spec R⊆S and U=Spec A⊆Z | `iV : Spec (.of R) ⟶ S`, `iU : Spec (.of A) ⟶ Z`, both with `IsOpenImmersion` |
| The induced R-algebra A and g(U)⊆V | `[Algebra R A]` and `hchart : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ iV = iU ≫ g` |
| s∈V represented by p | `p : PrimeSpectrum R`; the original point s is `iV p` |
| B=R_p | `Localization.AtPrime p.asIdeal` |
| m=pB | `IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)`; this equals pB by Mathlib `IsLocalization.AtPrime.map_eq_maximalIdeal` |
| k=B/m=κ(s) | `p.asIdeal.ResidueField`, definitionally `IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)`; the open immersion identifies it with the residue field at s |
| C=A⊗_R B | `localizedAffineCoordinateAlgebra R A p`, literally that tensor product |
| Canonical B action on C | `localizedAffineCoordinateAlgebra_algebra`, exactly `Algebra.TensorProduct.rightAlgebra` |
| F=C/mC | `localizedAffineFibreQuotient R A p`, literally quotient by the ideal mapped along `algebraMap B C` |
| Every prime P of C contracting to m | `∀ (P : Ideal C) [P.IsPrime] [P.LiesOver m]` in `hres`; `LiesOver` is equality of contraction |
| Canonical k action on C/P | `localizedAffinePrimeQuotient_algebra`, exactly Mathlib `Ideal.Quotient.algebraOfLiesOver P m`; the fraction ring inherits this scalar action |
| trdeg_k Frac(C/P)=0 | `Algebra.trdeg p.asIdeal.ResidueField (FractionRing (C ⧸ P)) = 0` in `hres` |

The open-immersion encoding is the usual parameterization of a chosen affine
open together with its specified coordinate ring. Its image is U or V. Conversely
every affine open chart supplies such an open immersion, and the containment
condition gives the commutative chart square. No affineness of Z or S is assumed.
All objects use the scheme universe u, so rings can be chosen in the same universe
as the affine charts. There is no separate smaller test-object universe.

Conclusions, in their order in the theorem:

| Node clause | Lean rendering |
| --- | --- |
| The canonical k structure on F | `∃ t : k →+* F` with `∀ b : B, t (IsLocalRing.residue B b) = algebraMap C F (algebraMap B C b)` |
| F≅C⊗_B k, canonically | `e₁ : F ≃+* (C ⊗[B] k)` and `e₁ ([c]) = c ⊗ₜ 1` for every c |
| C⊗_B k≅A⊗_R k, canonically | `e₂` and `e₂ ((a ⊗ₜ b) ⊗ₜ x) = a ⊗ₜ (residue B b * x)` |
| These are k-algebra isomorphisms | `∀ x : k, e₁ (t x) = 1 ⊗ₜ x` and `∀ x : k, e₂ (1 ⊗ₜ x) = 1 ⊗ₜ x`; a ring equivalence with these equations is exactly an algebra equivalence for the displayed k actions |
| U_s≅Spec F as k-schemes | `∃ eU : (Spec.map (ofHom (algebraMap R A))).fiber p ≅ Spec (.of F)` with equality after composing with `Spec.map (ofHom t)`; `Scheme.Spec.residueFieldIso` supplies the canonical κ(p) comparison, in the correct inverse direction |
| This is the canonical affine fibre identification | The second equation for `eU` identifies its composition with Spec of `A → C → F` with `.fiberι p`, so both pullback projections are specified |
| Primes P/mC correspond exactly to primes over m | Injectivity of `PrimeSpectrum.comap (algebraMap C F)`, and equality of its range with primes whose contraction along `algebraMap B C` equals m |
| The corresponding primes have residue field Frac(C/P) | For every Q in Spec F, the canonical `Ideal.ResidueField.map` from the residue field of its contracted prime P to Q's residue field is bijective. Mathlib's `Ideal.ResidueField` is canonically a fraction field of C/P. Its quotient residue-field map commutes with images of C, hence also with the k action defined by residue classes of B. |
| Spec F finite type over k | `LocallyOfFiniteType (Spec.map (ofHom t)) ∧ QuasiCompact (Spec.map (ofHom t))` |
| Every point closed | `∀ Q : PrimeSpectrum F, IsClosed ({Q} : Set (PrimeSpectrum F))` |
| Underlying space finite and discrete | `Finite (PrimeSpectrum F) ∧ DiscreteTopology (PrimeSpectrum F)` |
| The points in U over s form a finite set | `Set.Finite {z : Z | z ∈ Set.range iU ∧ g z = iV p}` |
| g quasi-finite at every such point in Z,S | `∀ z : Z, z ∈ Set.range iU → g z = iV p → g.IsQuasiFiniteAtPoint z` |
| No extra base assumptions | No dimension, generic algebraicity, Noetherian, properness or normality binder appears. |

The ring equivalences are represented by ring equivalences plus explicit scalar
compatibility equations, rather than introducing file-local algebra instances.
This is the full data of the requested k-algebra isomorphisms. The map t is not
arbitrary: the residue B→k is surjective and its displayed equation uniquely
determines t. Likewise e₁ is determined on the surjective quotient C→F, and e₂ on
pure tensors. The fibre equations determine the canonical pullback isomorphism.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map` (def-pc-scheme and def-weil-affine-spectrum).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`
  (def-weil-finite-type-morphism). Finite type means their conjunction.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: `Ideal.ResidueField`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`: `Ideal.Fiber`
  (def-weil-pbc-localization-at-prime). The theorem retains the node's A⊗k order;
  Mathlib's `Ideal.Fiber` uses the canonically isomorphic k⊗A order.
- `Mathlib.RingTheory.AlgebraicIndependent.Basic`: `Algebra.trdeg`
  (def-kun-transcendence-degree).
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField` (def-pc-scheme-fibre).
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `Scheme.Hom.IsQuasiFiniteAtPoint` (pqf-def-quasifinite), which uses
  `Algebra.IsQuasiFiniteAtPrime` from
  `WeilConjectures.RingTheory.QuasiFiniteAtPrime`.

Proof dependency imports are kept non-public. Their recorded Mathlib matches are
provided by the finite-type/fibre modules and explicit imports of Artinian,
Noetherian, Pullbacks, KrullDimension.Basic and TensorProduct.Maps. The recorded
`WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism` is imported for
its affine description of the canonical residue map. No separate dependency
module or private duplicate of a dependency definition is supplied.

Edge cases checked before and during statement writing:

- A=0, U empty, or an empty fibre: F=0 is allowed; hres quantifies over no primes,
  both spectra are empty, finite/discrete and closed-point clauses remain valid,
  and there is no quasi-finite point to check. No `Nontrivial A` or `Nontrivial F`.
- R=0: no p exists, exactly as no s in Spec R exists.
- R a field: B=R and the criterion is the usual zero-dimensional affine
  finite-type criterion. A=k[T] does not satisfy hres at the generic prime.
- Nonreduced A=k[ε]/(ε²): residue trdeg is zero; no reducedness assumption is added.
- A non-Noetherian base R is allowed: finiteness is only for the chosen affine
  fibre over the field, not for the base or the whole scheme.
- An infinite disjoint union of points in Z causes no erroneous global finiteness
  conclusion: the finite set is explicitly restricted to `Set.range iU`.
- Positive transcendence degree excludes the positive-dimensional fibre case;
  the hypothesis ranges over every prime above m, not only closed primes.

Searches (all via the prescribed msearch wrapper and direct read-only searches):

1. LeanFinder: "A locally finite type affine chart whose localized fibre residue
   fields have transcendence degree zero has finite discrete fibre and is quasi
   finite at each point". Eight hits, including `Algebra.quasiFinite_iff`,
   `AlgebraicGeometry.locallyQuasiFinite_iff`, and finite morphism results. None
   states this single-fibre criterion together with the canonical identifications.
2. Loogle: `"Algebra.trdeg", "QuasiFinite"`. Zero hits.
3. Mathlib grep: `quotient.*(Tensor|tensor)|(Tensor|tensor).*quotient` in RingTheory.
   Twenty-five hits, including `Algebra.TensorProduct.quotIdealMapEquivTensorQuot`
   and `tensorQuotientEquiv`. These give comparison APIs, not the complete theorem;
   the helper abbreviations merely name the actual rings built with these APIs.
4. LeanSearch: "A locally finite type affine fibre with algebraic residue fields
   is finite discrete and the morphism is quasi finite at every point of the fibre".
   Eight hits, all general quasi-finite predicates/constructors or the finite-type
   constructor. No exact match.
5. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
   `localizedAffine|residue.*criterion|residue.*quasi|trdeg.*QuasiFinite`, plus
   `grep -rn` for this exact node id in WeilConjectures: no statement of this node.
   The nearby `finite_residue_extension_trdeg_zero_of_quasiFinite` is the reverse
   direction. An exact-name search for all new declaration names in the upstream
   name inventory and both library roots found no clashes.

Validation: scompile.py compiled both the private sandbox probe and the actual
module against the live server build. Final result: no errors or warnings, with
`set_option autoImplicit false`. The sole postponed proof is the main theorem.
The first diagnostic was missing `Algebra k (C/P)` for the canonical quotient
instance; it was repaired with the existing `algebraOfLiesOver` construction,
without adding any mathematical assumption.

No STATEMENT-DISPUTED flag or node fault remains.

## Second reading by NB

The dispatcher's brief requires self-delivery, forbids starting other agents, and
assigns independent review to the maintainer. No independent worker reading is
claimed here. This section records the final in-thread re-reading of the node
and the full module, for the maintainer's independent reading.

The re-reading checked all hypothesis and conclusion pairs in the tables above.
It prompted explicit scalar-compatibility equations for both ring equivalences,
so their k-linearity is visible without relying on an unstated choice of scalar
action. Both fibre projections are now specified, using the canonical affine
residue-field comparison in the base projection. The prime correspondence uses
the actual quotient map and an exact range equality; its residue comparison uses
the actual induced residue-field map, not an unspecified isomorphism. The last
clause uses the original g, Z and S, rather than only the chart morphism. Empty
and nonreduced fibres remain included. No mismatch with the unchanged node
statement was found.
