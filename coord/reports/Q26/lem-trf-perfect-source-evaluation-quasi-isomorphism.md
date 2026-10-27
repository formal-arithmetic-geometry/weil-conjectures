## Worker report

Q26 states `lem-trf-perfect-source-evaluation-quasi-isomorphism` in
`Sheaf.Algebra.Homology.PerfectSourceEvaluationQuasiIsomorphism`.
The sole postponed proof is
`CochainComplex.perfect_source_evaluation_quasi_isomorphism`; its docstring gives
the complete seven-step proof, including the representative comparison and the
normalization of the actual derived arrow. The two auxiliary definitions have
real data. No statement correction or disputed mathematical assertion was found.

### Hypotheses and clauses

- A commutative ring is `(R : Type u) [CommRing R]`. Ordinary modules, equivalently
  the one-object-site presentation in the node, are `ModuleCat.{u} R`.
- All four arbitrary, potentially unbounded complexes are
  `(M F J I : CochainComplex (ModuleCat.{u} R) ℤ)`.
- Localization into the ordinary unbounded derived category is `DerivedCategory.Q`.
  Its canonical module-category localization and closed structure are inferred;
  no extra localization, resolution or size hypothesis is imposed.
- Perfectness of the derived source is
  `_hM : IsPerfectRingComplex (DerivedCategory.Q.obj M)`. This is exactly the
  existing bounded finite-projective model predicate, and says nothing about
  the terms of M itself.
- K-flatness is `_hF : (HomologicalComplex.quasiIso (ModuleCat.{u} R)
  (.up ℤ)).kFlat F`. The recorded predicate preserves quasi-isomorphisms under
  tensor; over the commutative ring it is the required K-flat predicate.
- K-injectivity of the two targets is `[J.IsKInjective] [I.IsKInjective]`.
- The prescribed coefficient replacement is `(q : F ⊗ J ⟶ I) [QuasiIso q]`.
  Native `⊗` on complexes is the direct-sum signed total tensor, not a product
  totalization. `moduleHomComplex M V` is the existing module-valued product
  total Hom with differential d_V h - (-1)^r h d_M.
- The existence of the displayed chain map is `∃ t : F ⊗ moduleHomComplex M J ⟶
  moduleHomComplex M I`. Being a morphism of complexes includes the differential
  identity. The following universally quantified equation specifies t on every
  homogeneous generator. In degrees p,r,s, the input is the `(p,r)` tensor
  inclusion of `f ⊗ₜ[R] h`; its s-component evaluated at x equals the degree
  `s + (p + r)` component of q on the `(p,s+r)` inclusion of
  `f ⊗ₜ[R] h(x)`. The equality witness `by omega` only reassociates integer
  degrees. There is no extra sign. Pure tensors span each tensor summand and
  product coordinates separate elements, so this condition specifies the
  canonical map rather than permitting an arbitrary successful arrow.
- Quasi-isomorphism and invertibility after localization are both recorded:
  `QuasiIso t ∧ IsIso (DerivedCategory.Q.map t)`.
- `eJ` and `eI` identify the localizations of the actual product Hom complexes
  with `(ihom (Q.obj M)).obj (Q.obj J)` and its I analogue. This is exactly
  `ordinaryModuleDerivedInternalHom R` in curried notation.
- `PerfectSourceHomModel M V e` fixes these isomorphisms by their counit. It
  requires the actual chain evaluation `M ⊗ moduleHomComplex M V ⟶ V`, with
  generator formula `(-1)^(p*r) h(x)`, and the equation comparing its localization
  through `Functor.LaxMonoidal.μ Q` with `ihom.ev`. The sign occurs because
  this existing closed structure places M first; after the native Koszul
  braiding it is the unsigned evaluation `h ⊗ x ↦ h(x)`. No evaluation map or
  Hom identification is chosen arbitrarily.
- `perfectSourceDerivedEvaluation` is a construction from the existing
  `MonoidalClosed.ihomTensorToIhom` and the existing localized Koszul braiding
  `DerivedMonoidal.braiding'`. It is the canonical comparison
  `QF ⊗ RHom(QM,QJ) ⟶ RHom(QM,QF ⊗ QJ)`.
- The final equation identifies `μ Q F Hom ≫ Q.map t ≫ eI.hom` with
  `(QF ◁ eJ.hom) ≫ perfectSourceDerivedEvaluation ... ≫
  (ihom (QM)).map (μ Q F J ≫ Q.map q)`.
  Thus it gives exactly the asserted canonical comparison, including the
  K-flat tensor comparison and coefficient identification through Qq. The lax
  tensorators are the existing native derived-tensor comparisons; under K-flatness
  of F the displayed ones are the required isomorphisms.
- There are no boundedness assumptions on the four complexes, no termwise
  projectivity hypothesis on M, and no Noetherian assumption on R.

### Dependency declarations used

All recorded statement dependencies were read with their full signatures and
docstrings. Public imports retain them.

| DAG node | Module and declaration |
| --- | --- |
| def-pc-tensor-complex-sheaves | Mathlib.Algebra.Homology.BifunctorShift; CochainComplex.mapBifunctor, specialized by the native complex tensor |
| def-pur-hom-complex | WeilConjectures.Algebra.Homology.HomComplex; CategoryTheory.homComplex (ringed-sheaf presentation) |
| def-sc-module-total-hom-complex | WeilConjectures.Algebra.Homology.ModuleHomComplex; CochainComplex.moduleHomComplex (ordinary-module product Hom) |
| def-weil-abstract-derived-category | Mathlib.Algebra.Homology.DerivedCategory.Basic; DerivedCategory and DerivedCategory.Q |
| def-pc-perfect-ring-complex | Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral; DerivedCategory.IsPerfectRingComplex |
| def-pc-module-kflat-complex | WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat; CategoryTheory.MorphismProperty.kFlat |
| def-pur-kinjective-complex | Mathlib.Algebra.Homology.HomotopyCategory.KInjective; CochainComplex.IsKInjective (the node's Mathlib match) |
| def-pur-derived-internal-hom | Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom; CategoryTheory.ordinaryModuleDerivedInternalHom |

The existing landed node `def-sc-module-total-hom-complex` is added to stmt_deps
as authorized by brief-stage2 §5. It is precisely the ordinary-module instance
needed here; the generic sheaf Hom interface is not copied or replaced. No new
node or dependency repair is necessary.

The canonical derived comparison additionally reuses
`MonoidalClosed.ihomTensorToIhom` from
`WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic`. Proof-only imports
provide the recorded projective Hom model, quasi-isomorphism invariance, finite
projective tensor-Hom equivalence, projective-source morphism representation,
bounded-flat K-flatness, K-flat tensor models, and native ringed tensor/adjunction
constraints. The proof-only uncurrying node has no usable Lean record yet; no
unrecorded declaration of it is used to type the statement.

### Sources and edge cases

Read Stacks `more-algebra.tex`, Tag 0BYM (explicit generator formula and differential),
0BYN (K-flat/K-injective model), and 0ATK case (1) (perfect source). The proof
route in the node replaces M by a bounded finite-projective source but does not
assume that M itself is such a source.

Checked M=0, F=0, J=I=0, and the zero ring: the formula and counit-normalization
reduce to the zero morphisms, and the displayed invertibility has the expected
zero-object interpretation. For M=R in degree zero the unsigned formula reduces
to q, as required. Nonzero and negative degrees were checked in the differential
and evaluation signs: signed source-first evaluation cancels the Koszul sign
when changed to Hom-first evaluation. The degree identity is s+(p+r)=p+(s+r).
An unbounded representative M of a perfect object is permitted because no
boundedness or projectivity instance is requested. Unbounded F,J,I cause no
infinite-support interchange in the statement: tensor uses direct sums and Hom
uses unrestricted products. No edge case forced a change to the node.

### Searches

All searches used the prescribed msearch wrapper or read-only rg/grep in the
specified source trees. No existing declaration states the whole node.

- LeanSearch: `For a perfect complex M the map F tensor Hom(M,J) to Hom(M,I) for K flat F and K injective J I is a quasi isomorphism`.
  Eight generic quasi-isomorphism/short-complex hits; no exact statement.
- LeanFinder: `Perfect source tensor evaluation on K flat and K injective representatives is a quasi isomorphism`.
  Eight generic K-injective resolution/flat exactness hits; no evaluation theorem.
- Loogle: `HomologicalComplex.QuasiIso, CochainComplex.moduleHomComplex`.
  The first name was rejected as unknown, so this was not treated as evidence
  of absence. Repeated as `QuasiIso, CochainComplex`: twelve generic
  quasi-isomorphism hits, including `DerivedCategory.isIso_Q_map_iff_quasiIso`,
  with no perfect-source evaluation statement.
- Mathlib grep through msearch: `tensor.*[Hh]om|[Hh]om.*tensor` in Algebra/Homology.
  Five monoidal tensor-object infrastructure hits; no exact theorem.
- Project rg in lean/Sheaf and lean/WeilConjectures:
  `perfect.*source|source.*evaluation|derived.*evaluation|evaluation comparison|tensor.*Hom|perfect.*Hom`.
  Found ProjectiveHomEvaluationModel, which requires a projective bounded-above
  source and does not state this arbitrary-representative theorem.
- Project grep for `perfect-source-evaluation|source.*evaluation.*quasi` and rg
  for the item id in lean/WeilConjectures found no existing theorem.
- Project rg for `moduleHomComplex` found the already landed ordinary product
  Hom construction, reused here instead of constructing another one.
- Project rg for `ihom.*[Tt]ensor|[Tt]ensor.*[Ii]hom` found the existing generic
  `MonoidalClosed.ihomTensorToIhom`, reused by the comparison helper.
- Project rg for the three delivered declaration names in both source trees
  and dag/lean_names_upstream.json found no declaration collision.

## Second reading by Q26

The dispatcher explicitly forbids starting other agents, so this is a second
self-reading rather than a claim of independent agent review. The maintainer's
independent review remains the delivery review prescribed in the brief.

Reopened the node and final module and checked every hypothesis and displayed
clause. The product Hom is the existing ordinary module construction, not the
native closed-Hom complex with a different sign convention. The canonical map
is pinned by all homogeneous coordinates. The derived equality includes both
Hom model identifications and the actual tensorator followed by Qq. The Hom
identifications are fixed by the signed evaluation equation and cannot be
replaced by unrelated isomorphisms. The helper uses the existing generic
comparison rather than duplicating it. All universes and variables are explicitly
bound, and `autoImplicit` is false. No mathematical mismatch or statement
correction was found; the only compilation warning found during this pass was
a long docstring line, subsequently wrapped to meet the 100-character limit.
