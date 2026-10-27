## Worker report

The module `Sheaf.RepresentationTheory.FiniteSubextensionContinuousCochains` constructs
continuous cochains on the actual tensor product Ω ⊗[E] W, the finite-subextension
subcomplex and its actual inclusion. The main statement is
`ContinuousCohomology.finiteSubextensionInclusion_quasiIso`. It includes the
quasi-isomorphism and the three explicit cohomological clauses. The final theorem
`finiteSubextensionInclusion_derived_isIso` says that Q of the underlying abelian-group
inclusion, extended by zero to integer degrees, is invertible in ordinary D(Ab).
Every theorem proof is `sorry`. Definitions have explicit data; no arbitrary map or
existence-choice model replaces the specified inclusion.

Sources read: the whole item node and its four proof steps; each original statement
dependency's node and recorded declaration; the current blueprint at
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3); Stacks
`etale-cohomology.tex`, section-continuous-group-cohomology (Tag 0DVG), displayed
continuous complex and differential; `derived.tex`, definition-unbounded-derived-category
(Tag 05RU). The current blueprint's paragraph (3) gives the direct-image argument;
this scalar analytic comparison remains the node's agent-formulated arithmetic
obligation, with exact higher-degree literature reference WANTED as recorded in the DAG.
No source-based statement correction was needed.

Hypotheses and objects, clause by clause:

- Prime ℓ: `(l : ℕ) [Fact l.Prime]`; Ω and its extending norm:
  `(Ω : Type u) [NormedField Ω] [NormedAlgebra ℚ_[l] Ω]
  [IsAlgClosure ℚ_[l] Ω]`. There is no completeness binder.
- Finite intermediate E: `(E : IntermediateField ℚ_[l] Ω)
  [FiniteDimensional ℚ_[l] E]`. This uses the restricted norm topology of Ω.
- Arbitrary profinite G: `(G : ProfiniteGrp.{v})`, encoding a compact Hausdorff totally
  disconnected topological group, without finite generation or cohomological bounds.
- Finite-dimensional norm-topological W and jointly continuous linear action:
  `(W : Type w) [AddCommGroup W] [Module E W] (ρ : G →* (W ≃ₗ[E] W))`
  and `hρ : Representation.IsContinuousCoefficient l E G W ρ`. The latter includes
  finite-dimensionality and joint continuity in the finite-extension module topology.
  Its source definition uses the unique extending spectral norm; this gives the same
  topology as the restricted norm on the intermediate field E.
- Scalar extension V_Ω: `finiteScalarTopRep` has underlying type `Ω ⊗[E] W`, topology
  `moduleTopology Ω (Ω ⊗[E] W)`, and the existing
  `Representation.coefficientScalarExtension E Ω G W ρ` action restricted to E.
  It acts trivially on Ω and through ρ on W. The module topology is the finite product
  norm topology in an E-basis of W. The named theorem
  `finiteScalarTopRep_jointlyContinuous` states the joint-continuity property needed
  to apply the dependency's continuous complex constructor.
- Finite F containing E: `F : IntermediateField E Ω` and `FiniteDimensional E F`.
  `finiteFieldCochains` consists of continuous ambient cochains whose every value lies
  in the range of `TensorProduct.map (IsScalarTower.toAlgHom E F Ω).toLinearMap
  (LinearMap.id : W →ₗ[E] W)`, the specified coefficient inclusion. A finite-dimensional
  F-vector space has its finite product topology, and this inclusion is a topological
  embedding: after a basis of W it is F^d → Ω^d, the product of the intermediate-field
  embeddings. Hence continuous ambient cochains with these values are exactly the
  included continuous V_F-valued cochains. No arbitrary coefficient map is used.
- C^n and the exact differential: `scalarContinuousComplex` specializes the dependency's
  `continuousInhomogeneousComplex` and `continuousInhomogeneousD`. The latter is the
  action term plus the signed `Fin.contractNth` faces. Its last face drops the last
  coordinate; at n=0 the sole signed face gives `g v - v`. Degree zero functions on
  `Fin 0 → G` identify canonically with V_Ω by evaluation.
- One finite field for an entire cochain: `finiteSubextensionCochains` is the supremum
  of the finite-field submodules, and `mem_finiteSubextensionCochains` states precisely
  that membership means existence of one finite F for every value. Two such submodules
  lie in their finite compositum, so this supremum is the union, not a completion or
  an unrestricted pointwise union with a different field at each input.
- The subcomplex: `finiteSubextensionCochains_d` states preservation by the specified
  differential. `finiteSubextensionComplex` restricts that actual differential and
  obtains square-zero by restricting the dependency's identity. Its construction
  does not choose a complex from a bare existence assertion.
- Actual inclusion i: `finiteSubextensionInclusion` is `CochainComplex.ofHom` of
  the submodule subtype maps. The commutation field is the restriction identity.
- Quasi-isomorphism: the first conjunct is
  `QuasiIso (finiteSubextensionInclusion l Ω E G W ρ hρ)`, with homology in abstract
  `ModuleCat E`. This is kernel modulo ordinary image, without closure of boundaries.
- Identity on V_Ω^G in degree zero: the second conjunct identifies invariant vectors v
  with the unique finite-subextension degree-zero cocycle whose values are v.
  As i is literally subtype inclusion, evaluation sends its image to the same v.
  Thus this specifies the identity on the common invariant kernel, not an arbitrary
  isomorphism between degree-zero cohomology objects.
- Boundary detection for every positive degree: the third conjunct quantifies n : ℕ,
  degree n+1 cocycles z, membership in the finite-field union, and an ambient primitive
  in degree n. Its conclusion supplies a primitive in that finite-field union.
- Representatives for every positive degree: the fourth conjunct quantifies the same
  arbitrary degrees and ambient cocycles, giving a finite-field cocycle c and ambient
  b with `z - c.val = d b`. Neither direction adds a degree bound.
- Negative degrees and D(Ab): `finiteSubextensionInclusionAb` forgets E-scalars using
  `(forget₂ (ModuleCat E) AddCommGrpCat).mapHomologicalComplex` and applies
  `HomologicalComplex.extendMap ... ComplexShape.embeddingUpNat`. Both integer
  complexes are literally zero in negative degrees. The final theorem states
  `IsIso (DerivedCategory.Q.map (finiteSubextensionInclusionAb ...))` with
  `[HasDerivedCategory.{x} AddCommGrpCat.{max u v w}]`. This is a choice of localization
  size under the size convention, not a new mathematical condition.
- Universes: u for Ω and intermediate E, v for G, w for W, and independent x for the
  derived localization. The abstract modules live in `max u v w`; there is no
  equality imposed on coefficient, group or vector-space universes.

Dependency declarations used:

- `Sheaf.RepresentationTheory.ContinuousCochainFiniteIndexTransfer`:
  `ContinuousCohomology.continuousInhomogeneousD`,
  `continuousInhomogeneousD_comp`, `continuousInhomogeneousComplex`, and
  `exists_continuousCochainFiniteIndexTransfer` (the last is the proof input).
  Their full docstrings and signatures were read. The source's differential and
  abstract-module category are reused, not privately defined again.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q` and its quasi-isomorphism inversion instance.
  `def-weil-size-convention` has a convention-only record; explicit universes implement it.
- `Sheaf.RepresentationTheory.LAdic`: `Representation.IsContinuousCoefficient` and
  `Representation.coefficientScalarExtension`. This already-landed definition node
  `def-pod-l-adic-representations` is added to stmt_deps because the signature and
  construction directly use its canonical action and continuity notion.
- Proof-only imports of the already-stated proof dependencies:
  `Sheaf.NumberTheory.Padics.FiniteSubfieldContinuousLinearRetraction` and
  `Sheaf.RepresentationTheory.LocalNormAlgclCocycleDescent`.
  The remaining proof dependency `lem-sfb-finite-scalar-cochain-retraction` has no
  recorded module in the read checkout; its stated coordinate computation is retained
  in the proof docstring. No new statement notion depends on its unavailable proof.
- Mathlib's existing `Submodule`, `TensorProduct.map`, `TopRep.of`, `ContRepresentation`,
  `moduleTopology`, `CochainComplex.of`, `CochainComplex.ofHom`, and extension-of-complex
  construction provide all other notions. The upstream `CochainComplex.SubcomplexFamily`
  was inspected but is specialized to equal coefficient/module universes and integer
  degrees; it is not the finite-subextension subcomplex defined by this node. The
  generic Mathlib constructors above avoid that restriction.

Edge cases checked before and during writing:

- W=0: the tensor spaces and cochain modules are zero, and all clauses remain meaningful.
- Degree zero: `Fin 0 → G` is a singleton, and the differential is exactly gv-v;
  the invariants are the common kernel. Every vector lies in a finite subextension.
- Positive degree one: n=0 in the third/fourth conjuncts; the primitive is a
  degree-zero cochain (one vector), not a nonexistent negative-degree cochain.
- Trivial G: no nontrivial-group hypothesis is imposed; its powers, including G^0,
  are nonempty and the standard unnormalized complex convention applies.
- E=ℚ_l and F=E: both are allowed by the IntermediateField quantifiers.
- F=Ω is the ambient complex; it is not mistakenly required to be finite-dimensional
  over E. The finite union alone ranges over finite F.
- Ω is not completed and W is not made discrete; no local compactness assumption on
  Ω tensor W is imposed. The topology is constructed before forming continuous maps.
- Transfer divides by a positive finite index in characteristic zero E; divisibility
  of that index by l causes no missing case or assumption.

Searches for existing statements and notions:

- `msearch.py leanfinder`: "The inclusion of continuous cochains valued in one finite
  p-adic subextension into all algebraic closure valued cochains is a quasi-isomorphism".
  Hits were generic Rep quasi-isomorphisms, continuous cohomology, and complex truncation
  results; none supplied this finite-subextension comparison.
- `msearch.py loogle`: `"continuousCohomology", "quasiIso"`: zero hits.
- `msearch.py leansearch`: "Finite subextension valued continuous cochains inclusion
  quasi isomorphism": eight generic resolution/truncation/Hom-complex results, no match.
- `msearch.py grep`: `(cochain|Cochain).*(IntermediateField|finiteSubextension)|`
  `(IntermediateField|finiteSubextension).*(cochain|Cochain)`: zero Mathlib matches.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf/RepresentationTheory` for finite/cochain,
  `coefficientScalarExtension`, `IsContinuousCoefficient`, and the proposed declaration
  names. The existing LAdic module provides the tensor action and continuity notion;
  the transfer module provides the specified complex. AcceleratedFiniteFieldCochainDifferences
  concerns scalar approximation against completion, while LocalNormAlgclCocycleDescent
  gives only a restriction-to-open-subgroup result. Neither is this global comparison.
  ProfiniteAlgclDerivedInvariantsComparison concerns a different condensed comparison
  and cites this arithmetic argument in its proof; it is not reused as a circular match.
- `rg` for the item ID in `lean/WeilConjectures`: no match. The proposed full declaration
  names were also checked against `dag/lean_names_upstream.json`: no collision.

No new independent notion requires a new definition node. The helper constructions and
named construction properties are precisely those introduced by this item's own text
and proof step 1, and all appear in its lean.declarations. No dependency module or
statement correction is delivered. No STATEMENT-DISPUTED fault was found.

Validation: every compile used the prescribed scompile.py wrapper. The module compiled
cleanly in sandbox mode and as its final library module, with explicit autoImplicit=false.
The delivery dry run is recorded below after it finishes.

## Second reading by NY

Second pass by the dispatched NY worker with the final Lean file and the item node open;
the maintainer's independent review follows delivery. No separate reviewer was invoked,
as the dispatch brief explicitly forbids starting other agents.

I checked the source differential against `continuousInhomogeneousD`: its contracted
last face deletes the last entry, so the sign and degree-zero action term agree. I
checked that `finiteScalarTopRep` has the existing tensor action and Ω-module topology,
that finite membership requires all values to lie in one tensor subspace, and that the
supremum's membership characterization rules out pointwise varying fields. The inclusion
components are actual subtype maps. The H0 clause evaluates to the same vector v;
the boundary clause has its source cocycle in the union and its primitive conclusion in
the union; the representative clause explicitly says dc=0 and z-c=db. The D(Ab) theorem
localizes the extension of that same map, rather than asserting an unspecified derived
isomorphism. I checked independent universes and the W=0, n=0, trivial G cases again.

During elaboration I repaired the continuous E-scalar-action coercion and the generic
complex-constructor restriction equations, added the standard abelian-category imports,
and made all hypotheses of both comparison theorems explicit in their signatures. These
changes did not alter the mathematical statement. All postponed helpers have source,
blueprint annotation and natural-language proofs, and match construction claims in the
item. The only DAG dependency addition is the already-landed canonical representation
node used by the statement. No hypothesis or clause mismatch remains in this reading.

Delivery dry run: `deliver2.py NY
lem-sfb-finite-subextension-continuous-cochain-quasi-isomorphism --no-push` returned
`OK (dry run): commit 7b8dc58d458 passes the preflight and compiles; nothing pushed`.
