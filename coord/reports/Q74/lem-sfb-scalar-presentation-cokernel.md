## Worker report

Module: `Sheaf.AlgebraicGeometry.ScalarPresentationCokernel`.
Declaration: `AlgebraicGeometry.ProEtale.scalar_presentation_cokernel`.
This delivery states the specified-presentation theorem, with one `sorry`, no new definitions,
no added hypotheses, and no change to the informal statement or its dependency lists.

The source is the current blueprint pullback proof, paragraph "Constructible complexes",
with the detailed six-step proof already in the node. I also read the local-model dependency,
the definitions of its scalar constructions, and the general presentation-mapping declarations
in Mathlib. The module docstring identifies the source and the theorem docstring carries all
six proof steps, including normalization, matrix entries, and the specified quotient arrow.

Hypotheses and clauses, in order:

- A commutative condensed ring: `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}`,
  `[MonObj Λ] [IsCommMonObj Λ]`. This is the unbundled form of the recorded transparent
  `Profinite.CondensedRing = Mon (Sheaf ... Ab)` abbreviation, with precisely the same
  multiplication and unit; it does not restrict Λ to continuous functions on a topological ring.
- Its scalar ring R = Λ(*): `scalarRingObj Λ`, literally `scalarSections.obj Λ` evaluated
  on the one-point profinite set. Scalar modules are `Mod Ab (scalarRingObj Λ)`, the
  dependency's internal-Ab encoding of ordinary R-modules. The unit object of Ab is ℤ,
  so a morphism `𝟙_ Ab ⟶ scalarRingObj Λ` is exactly a scalar, by its value at 1.
- Any scheme and its small pro-étale site: `U : Scheme.{u}` and
  `Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}`. This uses the recorded Mathlib site,
  retaining object universe u+1, morphism universe u, and coefficient universe u+1.
- The pulled-back coefficient ring is `condensedRingObj Λ U`, the underlying object of
  the recorded `coefficientRing U (Mon.mk Λ)`, with the existing transported ring structure.
- The functor E_U(Q) is exactly the public `finiteConstantScalarExtension Λ U` from
  the local-model dependency. Its definition is `(scalarConstant U).mapMod (scalarRingObj Λ)`
  followed by `Mod.extendScalars (scalarCoefficientHom Λ U)`. Thus it uses actual constant
  module sheaves, the counit-induced scalar map, and the actual relative tensor construction.
- The ranks m,n≥0 are unrestricted `m n : ℕ`; finite free modules are the recorded
  `Mod.finiteFree (scalarRingObj Λ) m/n` and `Mod.finiteFree (condensedRingObj Λ U) r`.
- The specified matrix is `A : Fin m → Fin n → (𝟙_ Ab ⟶ scalarRingObj Λ)`.
  This follows the existing scalarMatrix API: `A j i` is the node's a_ij (column first).
  The original map is explicitly `biproduct.matrix fun j i ↦ Mod.regularLift ... (A j i)`.
  No arbitrary map is substituted for the matrix.
- The specified module and quotient are the binders `P` and `q`. The hypotheses
  `hAq` and `hq : IsColimit (CokernelCofork.ofπ q hAq)` express exactly that q exhibits
  P as this matrix's cokernel, including factorization and uniqueness for all module maps.
- The canonical free comparisons are `e : ∀ r : ℕ, E_U(R^r) ≅ Λ_U^r`.
  Their first conjunct fixes them on every standard basis section: apply the monoidal
  constant functor to `one ≫ biproduct.ι ... j`, then `Mod.extendUnitHom`, and then
  `(e r).hom.hom`; the result is `one ≫ biproduct.ι ... j` in the coefficient free module.
  `extendUnitHom` is explicitly m↦1⊗m in the existing tensor construction. This states
  `1⊗e_j ↦ e_j`, so the isomorphisms are canonically pinned rather than arbitrary.
- The next conjunct identifies the transported original matrix with `scalarMatrix Λ U A`.
  That public dependency definition is `biproduct.matrix` with entries
  `Mod.regularLift ... (scalarSection Λ U (A j i))`. The existing `scalarSection` applies
  the unit comparison, the constant functor, and `scalarCoefficientHom` to that SAME entry.
  It therefore uses the canonical image of a_ij in Γ(U,Λ_U), with no replacement matrix.
- The displayed quotient after the free comparison is explicitly
  `(e n).inv ≫ (finiteConstantScalarExtension Λ U).map q`. The existential equation `h`
  says its composite with `scalarMatrix Λ U A` vanishes. The next conjunct is
  `Nonempty (IsColimit (CokernelCofork.ofπ ... h))`, the full cokernel universal property.
  `Nonempty` merely packages the Type-valued universal-property structure in a proposition.
- The final conclusion is an isomorphism `c : E_U(P) ≅ cokernel (scalarMatrix Λ U A)`.
  Its compatibility equation with the displayed quotient and `cokernel.π` records the
  canonical comparison for THIS q, not merely existence of an unrelated cokernel object.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing` (transparent unbundling).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its usual morphisms.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`,
  `AlgebraicGeometry.Scheme.ProEt.topology`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, `isCommMonObj_condensedRingObj`.
- `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`: `scalarSections`, `scalarRingObj`,
  `scalarConstant`, `scalarCoefficientHom`, `finiteConstantScalarExtension`, `scalarSection`,
  `scalarMatrix`; their public instances supply all required ring/monoidal structures.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `ModObj`, `Mod.regular`,
  the module-object category and morphisms.
- `WeilConjectures.CategoryTheory.ModuleObjects.Free`: `CategoryTheory.Mod.finiteFree`;
  the node's `IsFinitelyPresented` describes the same finite-free/cokernel notion, but a separate
  finite-presentation hypothesis is unnecessary because the specified cokernel supplies it.
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`: `Mod.extendUnitHom`.
  This existing public map pins the free comparisons, without copying a definition.

All recorded, stated proof-dependency modules are imported without `public`, unless already a
public statement dependency. Mathlib module sheafification and adjunction-limit modules are
included for the two Mathlib proof leaves. `def-sfb-modobj-extension` has no separate recorded
module, but the actual `Mod.extendScalars` construction is already used by the imported
local-model functor. No missing mathematical notion had to be introduced. The live coefficient import
interface is used unchanged.

Edge cases checked mathematically before writing:

- m=0: there are no relations, and the specified q is an isomorphism from R^n; its image
  yields the free coefficient module. The matrix has empty source and no excluded indices.
- n=0: a cokernel of R^m→0 is zero; its coefficient extension is zero as a left adjoint.
- m=n=0: all standard-basis normalization clauses have empty index and e(0) is the unique
  zero-object isomorphism; the cokernel universal property remains the whole assertion.
- The empty scheme is allowed: its sheaf module category is the zero category and all the
  claimed universal properties still hold.
- A zero coefficient ring, positive characteristic and torsion P are all allowed.
  Tensor right exactness, not flatness, is used. No nontriviality, field or flatness assumption
  appears in the theorem.
- The scalar entries are the original Λ(*) scalars in every case. A sheaf matrix with general
  nonconstant coefficients is not silently substituted.

Searches (2026-10-21):

- msearch.py leanfinder, "Constant module sheafification and extension of scalars preserve a
  specified finite scalar matrix cokernel presentation": 8 hits, including
  `SheafOfModules.presentationOfIsCokernelFree`, `SheafOfModules.Presentation.map`,
  `Presentation.map_generators_I`, `Presentation.map_relations_I`. These are generic
  sectionwise sheaf presentations and do not state the specified scalar comparison.
- msearch.py loogle, `SheafOfModules.Presentation.map`: 5 hits including the same mapping
  construction, its generator/relation equations and `map_π_eq`. I read the full source
  signatures and docstrings in `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`
  lines 109–194. They assume an already chosen colimit-preserving functor and unit isomorphism;
  neither the normalized scalar functor nor the specified matrix comparison is their conclusion.
- msearch.py leansearch, "Scalar extension of constant module sheaves preserves the specified
  matrix cokernel presentation": 8 hits, including `ModuleCat.ExtendScalars.obj'`,
  `Module.Presentation.cokernel`, `SheafOfModules.presentationOfIsCokernelFree`,
  `ModuleCat.extendRestrictScalarsAdj`, and `PresheafOfModules.Sheafify.map_smul`.
  No exact match: these supply ingredients, not this coefficient-sheaf diagram.
- msearch.py grep, `scalar.*presentation|constant.*[Cc]okernel|[Cc]okernel.*constant`,
  `Algebra/Category/ModuleCat`: 0 hits.
- rg over `lean/WeilConjectures` and `lean/Sheaf`, scalar-presentation/cokernel patterns and
  `finiteConstantScalarExtension`: the existing local-model module has private scalar free
  comparisons and matrix lemmas and proves a coverwise existential presentation result.
  It does not expose this theorem for a specified q. Its public functor and scalar matrix
  are reused directly. Other hits concern different scalar, derived or integral presentations.
- grep of the item id in `lean/WeilConjectures`: no hits. Search of the proposed declaration
  name in `dag/lean_names_upstream.json`, `lean/WeilConjectures`, `lean/Sheaf`: no hits.

No STATEMENT-DISPUTED flag, statement correction or new node is needed.

## Second reading by Q74

Author's second reading; no other agent was started, as the dispatcher brief requires.
I reopened the node and declaration and checked every line of the signature against the
clauses above. The distinction between the original specified q and an arbitrary isomorphic
presentation is preserved: q occurs in both the IsColimit conclusion and the final compatibility
with cokernel.π. The matrix entry normalization uses the same A, not newly chosen entries.
The explicit basis equation pins e, avoiding unnormalized free comparisons. The column-first
API agrees with the node's row-first notation via A j i = a_ij. The source and target of every
comparison are internal module objects over exactly the dependency rings, and all universes
and variables are explicitly bound. No mismatch requiring a node change was found.

## Repair of returned delivery

The maintainer returned head `3bf39c79b1f5` for H13: the extra performance repair of
`ContinuousCoefficientCommRing` was unnecessary and removed a deliberate public
re-export of `ModuleObject.BaseChangeTheorems.MorphismDefs`. Its rewritten dependency
record also named `CondensedRing.boundedConstructibleBaseChange`, which that reduced
import interface no longer exported.

Removed both the coefficient module and the
`def-weil-pbc-condensed-e-module-category` node from this delivery packet. They are
therefore left exactly as on the live branch, including the maintainer's recorded
binding and its deliberate public re-export. There are no dependency modules or
dependency record changes in this repaired delivery.

The scalar-presentation module and its node record are retained byte-for-byte from
the returned packet, as the independent review approved their mathematics and
compilation. Comparison with the current local live node found only its new `lean`
record differs; the statement and dependency lists are unchanged. The delivery
wrapper rebases the packet onto the current server branch.

The required initial dry run on the saved packet passed at `2f3e910414b`. That result
checked the superseded two-file packet; the repaired single-file packet is checked
afresh against the live coefficient interface before delivery.

Repaired-packet self-check: the standalone item compiled cleanly through `scompile.py`
against the unchanged live dependency (13.3 seconds in the sandbox phase and 8.6 seconds
in the library phase). Its recorded signature matches the theorem verbatim; the module
has exactly one `sorry`, explicit universe and variables, and no line over 100 characters.
The packet contains exactly one Lean module and one node. The basis normalization,
the original scalar entries, the given quotient q, its cokernel universal property and
the final quotient-compatible isomorphism were reread and are unchanged.
