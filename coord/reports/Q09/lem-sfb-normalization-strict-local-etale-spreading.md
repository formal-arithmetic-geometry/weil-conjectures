## Worker report

The module `Sheaf.RingTheory.NormalizationStrictLocalEtaleSpreading` states
`Algebra.normalization_strictLocal_etale_spreading`, with proof `sorry`, and constructs
its two canonical tensor maps as real definitions. The node is unchanged except for `lean`.
No new node, dependency repair, statement correction or disputed statement is needed.

Hypotheses, in the order of the node:

- Commutative Noetherian B: `(B : Type u) [CommRing B] [IsNoetherianRing B]`.
- Finite B-algebra C: `(C : Type v) [CommRing C] [Algebra B C] [Module.Finite B C]`.
- All prime local rings of C are integrally closed domains: `hnormal`, with exactly
  `∀ (p : Ideal C) [p.IsPrime], IsDomain (Localization.AtPrime p) ∧
  IsIntegrallyClosed (Localization.AtPrime p)`; no domain or connectedness of C is assumed.
- Element g with injective multiplication: `(g : C)` and
  `hg : Function.Injective (fun c : C ↦ g * c)`.
- C_g: `Localization.Away g`, carrying its canonical C-algebra structure.
- Finite etale C_g-algebra F: `[Algebra (Localization.Away g) F]`,
  `[Module.Finite (Localization.Away g) F]`, `[Algebra.Etale (Localization.Away g) F]`.
  Ring-map etaleness and affine-scheme etaleness are interchangeable here by Mathlib's
  `HasRingHomProperty @AlgebraicGeometry.Etale RingHom.Etale` (the project's stated convention).
- E is exactly `integralClosure C F`, not a freely chosen finite model. Its membership
  definition is the monic-polynomial condition in the node. C→F and B→F are bound as
  compatible algebra structures by `IsScalarTower C (Localization.Away g) F` and
  `IsScalarTower B C F`. These express composite structural maps, adding no mathematical
  assumption: the composites always carry precisely these structures.
- The strict-local part is universally quantified after the unconditional assertions.
  `v : Ideal B` and `[v.IsPrime]` specify the base point. Put R = `Localization.AtPrime v`.
  `K`, its field structure, residue-field algebra structure, `IsSepClosure`, and its
  compatible R-algebra structure specify the separable closure of the residue field
  selected by the geometric point. The strict localization depends on this separable
  closure, not on any transcendental extension of the geometric residue field.
  `A`, its compatible R- and B-algebra structures, and
  `StrictHenselizationPresentationIn.{u,s} R K A` use exactly the recorded definition of
  geometric strict localization, including its pointed-etale colimit and structural map.
  No merely strictly henselian algebra or arbitrary faithfully flat algebra replaces it.
- Etaleness after strict localization: `(normalizationModelBaseChangeMap B C F A).Etale`.
  The map sends `c ⊗ a` to `algebraMap C E c ⊗ a`; it is the specified map in the node.

Conclusions, in the order of the node:

- E finite over C: `Module.Finite C (integralClosure C F)`.
- E finitely presented as a C-algebra:
  `Algebra.FinitePresentation C (integralClosure C F)`.
- Canonical localization isomorphism E[1/g] ≃ F:
  `IsLocalization.Away (algebraMap C (integralClosure C F) g) F`.
  The algebra structure E→F is the actual subalgebra inclusion. By
  `IsLocalization.algEquiv` this property gives the unique E-algebra isomorphism from
  `Localization.Away (algebraMap C E g)` to F that extends the inclusion. Its compatibility
  with C_g follows from the localization uniqueness property for C→C_g: both maps agree
  on C and send inverse powers of g to the same inverse powers. Thus it is precisely the
  canonical C_g-algebra isomorphism, not the existence of an unrelated ring equivalence.
- Injective C→C_g: `Function.Injective (algebraMap C (Localization.Away g))`.
- Closure of C in C_g is its image: `integralClosure C (Localization.Away g) = ⊥`.
  The bottom C-subalgebra of C_g is the image of the structural map; it does not mean
  the zero ideal or the zero subring.
- Etaleness over B_v:
  `(normalizationModelBaseChangeMap B C F (Localization.AtPrime v)).Etale`.
- Neighbourhood: `∃ h : B, h ∉ v ∧ ...`, with no requirement that h be a nonunit.
- Finite etale neighbourhood model: the `.Finite` and `.Etale` properties of
  `normalizationModelBaseChangeMap B C F (Localization.Away h)`. `RingHom.Finite` uses
  finite generation over the source ring via precisely this ring map.
- Restriction along g is the base change of F→C_g: the final `@IsLocalization` has source
  `E ⊗[B] B[1/h]`, powers of `algebraMap C E g ⊗ 1`, and target `F ⊗[B] B[1/h]`.
  Its algebra structure is explicitly `.toAlgebra` of `normalizationCoverBaseChangeMap`,
  which sends `e ⊗ d` to `(e : F) ⊗ d`. Consequently its unique localization equivalence
  sends `(e ⊗ d)/(g ⊗ 1)^n` to `(e/g^n) ⊗ d` through the preceding canonical comparison.
  The analogous canonical localization of `C ⊗ B[1/h]` is `C_g ⊗ B[1/h]`; commutation
  with it follows on pure tensors and then inverse powers of g. This is the claimed
  equality of the restricted cover with the base-changed original cover. No arbitrary
  isomorphism or replacement map is quantified.

Dependencies read and reused:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  together with `IsDomain` and the prescribed inline prime-local normality condition.
- `Mathlib.GroupTheory.MonoidLocalization.Away` and
  `Mathlib.RingTheory.Localization.Away.Basic`: `Localization.Away`, `IsLocalization.Away`.
- `Mathlib.CategoryTheory.MorphismProperty.Comma` / `OverAdjunction`:
  `MorphismProperty.Over`, `MorphismProperty.Over.pullback`. The finite-etale node has
  only a Mathlib match and needs no duplicate declaration. Its two properties here are
  the finite-module and etale predicates on the affine algebra; no FEt category object
  is required by this ring-theoretic statement. The module giving its match is imported.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure` and `IsIntegral`.
- `Sheaf.RingTheory.StrictHenselizationPresentationIn`:
  `Algebra.StrictHenselizationPresentationIn`, its pointed-etale diagram and cocone.
- `Mathlib.LinearAlgebra.TensorProduct.Defs` and
  `Mathlib.RingTheory.TensorProduct.Maps`: `TensorProduct`, `Algebra.TensorProduct.map`.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`.

Every recorded proof-dependency module is also imported (ordinary imports, where not
already public for a statement dependency). The theorem docstring carries the eight
proof steps, their dependencies, the denominator-clearing formula, faithful-flat descent,
the finite-subset localization system, and the tensor comparison. The two helpers belong
to the canonical maps in this node and have its source/blueprint docstrings and lean records.
Their data are directly constructed with `Algebra.TensorProduct.map`; there is no choice,
postponed definition proof, hidden assumption or extra unrecorded theorem.

Edge cases checked:

- C may be the zero ring. Normality is vacuous, multiplication by g is injective on a
  singleton, C_g and F and E are zero, and both finiteness claims and the localization
  universal properties hold. No `Nontrivial C` appears.
- F may be zero even if C is nonzero: this is the empty finite etale cover. E is zero;
  no injectivity of C→F is asserted or needed. E→F is the actual subring inclusion.
- A disconnected normal C is allowed. No component is selected by a binder.
- If g=0, injective multiplication forces C to be zero; g=1 is allowed without change.
- B may be zero: the conditional strict-local portion has no prime v to test; the
  unconditional portion still applies.
- h=1 and the empty finite subset in the descent system are allowed.
- Universes u,v,w for B,C,F are explicit and independent. K,A and the pointed-etale
  diagram lie in `Type (max u s)`, which contains the base universe. There is no small
  independent universe making the strict-henselization test category vacuous, and no
  imposed equality among the base, model and cover universes.

Searches performed with the prescribed wrapper:

- LeanFinder: "Finite normalization model of a finite etale localization and etaleness
  spreads from strict henselization to a principal open neighbourhood". Eight hits,
  headed by `Algebra.exists_etale_of_isEtaleAt` and `RingHom.Etale.ofLocalizationSpan`.
  They give etale-locus localizations or locality, not normalization finiteness together
  with strict-local descent to an open of the base.
- Loogle: `"integralClosure", "Etale"`. One hit:
  `mem_adjoin_map_integralClosure_of_isStandardEtale`, a different integral-closure
  comparison without the finite normalization or spreading conclusions.
- Mathlib grep: `(normaliz|integralClosure).*(strictHensel|neighbou|IsEtale)`: zero hits.
- Direct `rg` of the corresponding patterns in the project RingTheory modules and of
  all proposed full names in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no existing assembled statement or name collision.
  Integral-closure matches in other modules state separate component or field results.
- `grep -rn "lem-sfb-normalization-strict-local-etale-spreading" lean/WeilConjectures`,
  and the corresponding project-source search: no declaration for this node.

Sources checked directly in `literature/stacks-project/`: `algebra.tex`,
`lemma-Noetherian-normal-domain-finite-separable-extension` (032L) and
`lemma-integral-closure-commutes-colim-smooth` (0CBF); `descent.tex`,
`lemma-descending-property-etale` (02VN); `limits.tex`, `lemma-descend-etale` (07RP).
The finite-normalization and dense-open proof dependencies were read in the actual
`WeilConjectures` modules. The source agrees with the node; no correction is required.

Validation: `scompile.py Q09 lem-sfb-normalization-strict-local-etale-spreading <module>`
compiled both its sandbox probe and its actual library module without errors or warnings.
Every variable and universe is explicitly bound. There is one named postponed theorem,
and its proof is solely `sorry`. All source lines are at most 100 characters.

## Second reading by Q09

This is the dispatcher's single worker doing a separate statement audit, not a claim of
independent review by a second agent. The brief prohibits starting agents; the maintainer
will perform the independent reading of this delivery.

Re-read the node against the full final signature. The normality binder is prime-local
normality, not domain normality of C. The nonzero-divisor condition is injective
multiplication, not merely `g ≠ 0`. F is finite as a C_g-module, not finite as a set.
Both module finiteness and algebra finite presentation of E are present. The closure
comparison is with the bottom subalgebra (the image), and injectivity of C→C_g is explicit.
The strict-local hypothesis retains the specified colimit presentation and compatible
base map, rather than replacing it by strict henselianity alone. Both etaleness over B_v
and finite etaleness on a principal B-neighbourhood occur in the conclusion. The last
localization uses the actual tensor inclusion, so it retains the original cover and its
canonical comparison. No connectedness, nonemptiness, field hypothesis on B or C, or
nontriviality assumption slipped in. No mismatch requiring a statement correction was found.
