## Worker report

The module `Sheaf.RepresentationTheory.CharZeroDifferentiationHom` states
`AlgebraicGeometry.charZero_differentiation_hom`, with one `sorry` and no new data definitions.
The statement of the DAG node and the complete Lean theorem signature are unchanged.
The added statement dependencies are `def-sfb-hopf-action-module-data`,
`def-sfb-affine-coordinate-hopf-algebra`, and `def-wf-lie-algebra-derivation`.
They own the coaction predicates, canonical coordinate Hopf structure, and canonical Lie
module/bracket/tangent-point construction. The two theorem dependencies rejected by the
immutable-head review have been removed from `stmt_deps`.

Source read: Milne, Algebraic Groups (2017), printed pp.190--196 and 208 (PDF pp.202--208
and 220), especially Proposition 10.15, Theorem 10.23, Propositions 10.28--10.31, and §10l.
The derivation correspondence is explicitly described on printed pp.195--196. The graph
stabilizer argument in the node extends the subspace stabilizer statement of Proposition
10.31 to a linear map between two representations. The seven proof steps are reproduced
in the theorem docstring, including all node citations.

Hypotheses and clauses, in statement order:

- Algebraically closed characteristic-zero field: `(F : Type u) [Field F] [IsAlgClosed F]
  [CharZero F]`. No particular algebraic closure is chosen, since the node only assumes
  algebraic closedness of F.
- Group scheme over F: `(G : Scheme.{u}) [G.Over (Spec (.of F))]
  [GrpObj (G.asOver (Spec (.of F)))]`. This is the group-object convention of
  `def-sc-group-scheme`, not a group of F-points replacing the group scheme.
- Affine, smooth and connected: `[IsAffine G]`, `[Smooth (G ↘ Spec (.of F))]`,
  `[ConnectedSpace G]`. Connected includes nonemptiness.
- Finite type: `[LocallyOfFiniteType (G ↘ Spec (.of F))]` and
  `[QuasiCompact (G ↘ Spec (.of F))]`, exactly the recorded conjunction.
- Tangent space at the identity: the existing `GrpObj.Lie (G.asOver (Spec (.of F)))`.
  `GrpObj.lieEquivTangent` sends it to the actual dual-number point over F reducing
  to the identity. This is the upstream construction assigned to
  `def-wf-lie-algebra-derivation`, with the additive and scalar structures from
  Lie.Basic/Lie.Ring and the mixed-commutator bracket from Lie.Bracket.
  The statement does not use the residue-field tangent equivalence.
- Finite dimension: the initial conclusion is `FiniteDimensional F (GrpObj.Lie ...)`.
- Canonical tangent derivation: `δ` is an F-linear map into the linear dual of `Γ(G, ⊤)`.
  Its first formula evaluates the coordinate ring map of the actual upstream
  `GrpObj.lieEquivTangent` point, using `Scheme.ΓSpecIso`, and says it is
  `TrivSqZeroExt.inl (Coalgebra.counit a) + TrivSqZeroExt.inr (δ x a)`.
  `Function.Injective δ` and the following range iff identify it with exactly the
  linear maps satisfying the counit Leibniz formula; no tangent vectors are lost.
- Left-invariant derivation and Lie bracket: `D` is a Lie homomorphism into
  `Derivation F Γ(G, ⊤) Γ(G, ⊤)` with its existing commutator bracket. Its formula
  is `(TensorProduct.rid ...).toLinearMap ∘ₗ (δ x).lTensor ... ∘ₗ Coalgebra.comul`.
  The next clauses state left invariance, `counit ∘ D = δ`, and surjectivity onto
  precisely the left-invariant derivations. This pins the existing tangent bracket
  to the bracket specified by the node, without assuming their agreement.
- Finite-dimensional rational representations: arbitrary `M : Type v` and `N : Type w`,
  each with `AddCommGroup`, `Module F`, and `FiniteDimensional F`. Their maps `αM, αN`
  have the required right-coaction types. The four implication hypotheses are the
  existing `HopfAction.Coassociative` and `HopfAction.Counital` predicates for both maps.
  These expand to the coassociativity and counit equations of the node.
- Differential is linear: the conclusion provides `drM, drN : Lie G →ₗ[F] Module.End ...`.
  Their displayed contraction formulas determine them uniquely from `αM, αN, δ`.
- Differential preserves brackets: each next clause says
  `dr ⁅x,y⁆ = (dr x).comp (dr y) - (dr y).comp (dr x)`. This explicitly uses the
  commutator on endomorphisms, avoiding a file-local Lie instance.
- Dual-number characterization: for each x, an algebra homomorphism g is required whose
  underlying ring homomorphism equals the coordinate map of the actual tangent point.
  Evaluation of each coaction at g is respectively
  `m ⊗ₜ[F] 1 + drM x m ⊗ₜ[F] DualNumber.eps` and the analogous N formula.
  The existential g has an exact equality to the canonical map, not an arbitrary action.
- Every F-linear map: `∀ f : M →ₗ[F] N`. The first iff is exactly
  `αN ∘ₗ f = f.rTensor Γ(G, ⊤) ∘ₗ αM` iff
  `∀ x, f ∘ₗ drM x = drN x ∘ₗ f`.
- Every commutative F-algebra extension: the second iff identifies the same coaction
  equality with the evaluation square for every `[CommRing R] [Algebra F R]` and every
  `g : Γ(G, ⊤) →ₐ[F] R`. The square is tested on every `m ⊗ 1`; R-linearity then gives
  all of `M ⊗[F] R`. The formula is the coaction dictionary's action, rather than an
  unspecified abstract group representation. `R : Type (max u r)` admits algebras in
  every containing universe; when r is larger, the lifted universal point still detects
  equality in the coordinate algebra. M and N have independent universes v and w.

Dependency declarations read and used:

- `Field` in Mathlib.Algebra.Field.Defs; `IsAlgClosed` in
  Mathlib.FieldTheory.IsAlgClosed.Basic; `CharZero` is the standard characteristic class.
- `CategoryTheory.GrpObj` in Mathlib.CategoryTheory.Monoidal.Grp, with the group-scheme
  interpretation documented in WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `LocallyOfFiniteType`, `QuasiCompact`, and `Smooth` in the identically named modules
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType, QuasiCompact, and Smooth.
- `ConnectedSpace` in Mathlib.Topology.Connected.Basic.
- `schemeTangentSpace`, its additive/module instances, and `schemeTangentMap` in
  WeilConjectures.AlgebraicGeometry.SchemeTangentSpace (full signatures read).
- `DualNumber` and `DualNumber.eps` in Mathlib.Algebra.DualNumber.
- `LieRing`, `LieAlgebra`, `LieHom` in Mathlib.Algebra.Lie.Basic, and the Lie structures
  on `Derivation` in Mathlib.RingTheory.Derivation.Lie.
- `GrpObj.Lie` in WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Basic;
  `GrpObj.lieEquivTangent` and the canonical bracket in the upstream .Lie.Bracket;
  the additive/module instances from .Lie.Basic/.Lie.Ring, and the bracket/LieRing/
  LieAlgebra instances from .Lie.Bracket. These are recorded by the repaired
  `def-wf-lie-algebra-derivation` record; no identity-tangent equivalence is imported.
- `HopfAction.Coassociative` and `HopfAction.Counital` in
  Sheaf.RingTheory.HopfActionModuleData; `HopfAction.coordinateHopfAlgebra` in
  Sheaf.AlgebraicGeometry.HopfCoactionLinearization. The latter reuses Mathlib's
  canonical affine group coordinate Hopf algebra, with the unbundled scalar field.

The already recorded proof modules are imported privately:
AffineFiniteTypeAlgebra, GroupScheme.Defs, LocallyAlgebraicGroupIdentityComponent,
OpenImmersion, RationalTangentCotangentDuality. Lie and SchemeTangentSpace are already
public statement imports. The comodule dictionary, Frobenius smooth-image lemma and
smooth-subgroup tangent-generation lemma currently have no recorded Lean declarations;
these are proof-only prerequisites, so no independent theorem is restated in this
stage-2 statement delivery.

Edge cases checked before and after writing:

- M = 0, N = 0, and either one zero: the universal vector-space binders do not require
  nontriviality or a positive dimension. The formulas give the unique maps and empty
  matrix equations, as the node explicitly requires.
- The trivial group: its Lie algebra is zero, both differentials vanish, and all maps
  between trivial rational representations are equivariant. The theorem includes it.
- The empty scheme is excluded by connectedness and by the group identity, just as in
  the node. No extra nonempty or nontrivial-vector-space hypothesis is added.
- Connectedness and characteristic zero are essential: nontrivial finite constant groups
  in characteristic zero have zero Lie algebra but nontrivial representations; Frobenius
  twists in positive characteristic have zero differential but nontrivial action.
- Noncommutative G is allowed: no cocommutativity is assumed. D and dr explicitly use
  commutators, so the bracket is not accidentally zero.
- General F-algebras, including the zero algebra and nonreduced dual numbers, are tested.
  The universal algebra point recovers the actual coaction square.
- Neither the invariant derivation space nor any representation is assumed finite
  dimensional in a place where finite dimension should instead be concluded; only M,N
  have the stipulated finite-dimensional hypotheses.

Searches actually run (also logged by msearch in this sandbox):

1. leanfinder: "Differentiation of rational representations of a connected algebraic
   group in characteristic zero is fully faithful". Eight hits, including
   Algebra.SubmersivePresentation.aevalDifferentialEquiv_apply and differential-field
   instances. None states this algebraic-group comparison.
2. loogle: `"differential", "Representation"`. Zero hits.
3. msearch grep: `differentiation|counitDerivation|invariantDerivation|rationalRepresentation`.
   Twenty-five hits, chiefly manifold left-invariant derivations and analytic derivatives;
   no algebraic-group statement.
4. leansearch: "A linear map between rational representations of a connected algebraic
   group in characteristic zero is equivariant if and only if it commutes with the Lie
   algebra action". Eight hits. Representation.linHom.mem_invariants_iff_comm concerns
   an abstract group action, and LieModule.maxTrivLinearMapEquivLieModuleHom concerns an
   already given Lie action; neither compares these two actions by differentiation.
5. rg in lean/WeilConjectures and lean/Sheaf for coactions, rational representations,
   counit derivations, differentiation and equivariant/differential comparisons.
   Found the reusable HopfAction predicates and coordinate instance, upstream GrpObj.Lie
   and its tangent equivalence, and matrix-specific RationalHom.differential. No theorem
   states the present comparison for arbitrary finite-dimensional comodules.
6. grep -rn for the exact item id in lean/WeilConjectures: no hits. Target declaration
   name search and source inspection found no existing declaration of this statement.
7. DAG searches identified the already landed HopfAction and tangent-equivalence nodes.
   Traversing their statement and proof dependencies confirmed that adding them creates
   no path back to this item.

No mathematical statement correction or STATEMENT-DISPUTED flag is needed.
The definition ownership repairs requested by the return are described below.

## Second reading by Q08

Final worker audit; the maintainer supplies the independent review of this delivery.
Re-read the unchanged node and the complete final signature. The field hypotheses, affine
smooth connected finite-type group, canonical tangent space and commutator bracket,
finite-dimensional coactions, linear bracket-preserving differentials, dual-number
normalization, both directions of the intertwining criterion, and the all-algebra-points
clause are all present as detailed above. No basis, embedding in GL_n, connected subgroup,
preselected differential, or a restriction to F-points has become an extra hypothesis.
The quantified δ, D and dr are conclusions with exact characterizations, never assumptions.

During elaboration, replaced the bundled Over parameter by the equivalent Scheme.Over
encoding because instance inference could not identify its repackaged group-object
structure. Replaced an implicit endomorphism Lie instance by the explicit commutator
identity. The dual-number algebra map is tied to the actual tangent point by equality;
it is not an arbitrary lift. These repairs changed no mathematical hypothesis or clause.
Every universe is explicit and autoImplicit is disabled. The module has one named theorem
with its complete proof docstring and one sorry, no local definitions or local instances.
All lines are at most 100 characters.

Validation: the prescribed scompile.py compiled both its sandbox module and its library
module cleanly. The required deliver2.py preflight and final per-file compilation are run
after this report is written; their authoritative result is the delivery output.


## New nodes

`def-sfb-affine-coordinate-hopf-algebra` is an existing:true definition node owning
`HopfAction.affineCoordinateHopfAlgebra` and `HopfAction.coordinateHopfAlgebra` in the
already landed module `Sheaf.AlgebraicGeometry.HopfCoactionLinearization`.
Nothing is moved or copied. The bundled-base helper is exactly Mathlib's canonical
coordinate Hopf instance; the second specializes it to the unbundled field. In particular,
the Coalgebra/Algebra instances in the theorem signature are real data inferred from this
structure, never a choice from `hopfCoactionLinearization`. Its statement gives the same
comultiplication, counit and antipode dual to the group laws, over a commutative base ring
and in its field specialization, without finite-type, smoothness or connectedness conditions.
Source: Mathlib AlgebraicGeometry/Group/Affine.lean:336--343 and Stacks 022S, with the
existing helper signatures at HopfCoactionLinearization.lean:29--38. The three search kinds
were rerun: LeanSearch and LeanFinder each returned eight generic Hopf-algebra hits;
Mathlib grep found the canonical instance at Affine.lean:338. Direct source grep located
both wrappers only in the recorded Sheaf module. DAG grep found no definition node owning
them; only the theorem node listed their names. Blueprint search returned zero matches
for coordinate Hopf. The actual search log entries are retained in mathlib_searches.
The affine spectrum and group-scheme nodes supply the underlying notions. Edge cases:
the trivial affine group, arbitrary commutative base ring (including the zero ring), and
noncommutative group schemes are admitted; no cocommutativity condition is added.

## Dependency modules

`def-wf-lie-algebra-derivation` receives a lean-only existing:true record repair under
brief-stage2 §1(B), as requested in return (b). No new module is written. Its old primary
record exposed only `AlgebraicGeometry.tangentGroup`; the unchanged upstream audit and name
map already assign `GrpObj.Lie` to this definition node. The repaired record exposes the
existing `GrpObj.Lie`, additive and base-ring module instances, `GrpObj.lieEquivTangent`,
and bracket/LieRing/LieAlgebra instances through the existing upstream Lie.Bracket module;
it retains tangentGroup. Lie.Basic defines Hom(e*Omega,O), Lie.Ring supplies the R action
through GammaSpecIso, and Lie.Bracket defines the tangent-point equivalence and transports
the mixed commutator to Lie. This is precisely the general group-scheme clause of the
current blueprint's def-wf-lie-algebra-derivation (read in literature/blueprint/latest).
The remainder of the dependency node is byte-for-byte equivalent as JSON data to current
main, including all its matrix-action realizations in lean_audit. This repair supplies the
interface needed by the unchanged consumer without importing or citing
`lem-ag-lie-identity-tangent-equiv`.

## Returned delivery repair

Immutable head reviewed: 449c1263376c. The initial saved-packet dry run passed at de2c2b65b2a;
that gate result did not resolve the independent H2 finding, so both requested repairs were
made before delivery. Point (a): replace the statement citation of
lem-sfb-hopf-coaction-linearization by the new existing:true Hopf definition node. Point (b):
replace lem-ag-lie-identity-tangent-equiv by def-wf-lie-algebra-derivation, with its lean-only
record repaired as above. H9: remove the unused LieIdentityTangentEquiv public import and
update the module overview to name lieEquivTangent. No theorem clause or hypothesis changes.

Second reading of the repaired packet by Q08 (self-check; the maintainer supplies the
independent review): re-read both existing helper definitions, Lie.Basic, Lie.Ring and
Lie.Bracket, their full signatures/docstrings, the dependency record, the current blueprint
and the consumer. A server #check probe confirmed the additive, base-field module, bracket,
LieRing, LieAlgebra and tangent-equivalence names. One guessed global-scalar instance name
was absent; it was removed from the probe and is not recorded in the delivery. Each recorded
instance name is confirmed. The theorem signature matches the saved packet and its lean
statement verbatim. The existing hypothesis/clause and edge-case audit above still applies,
including M=0, N=0 and trivial G. All item fields other than lean and stmt_deps match current
main; only lean changes on the repaired dependency. Every new-node field was checked against
brief-stage2 §5 and the concrete preflight diagnostic (which additionally requires import_flags). No additional definition, theorem, sorry or strengthened assumption is added.

Validation of the repaired packet: run scompile.py on the delivered consumer module, then
rerun deliver2.py --no-push and the final delivery. The final wrapper output is authoritative.


Preflight repair: the first repaired-packet dry run required import_flags on the new node
and a primary declaration physically present in its recorded module. Added import_flags=[]
and made lieEquivTangent in Lie.Bracket the primary declaration of the dependency record.
That module defines the bracket/LieRing/LieAlgebra instances and publicly imports the Lie
module structures; all the other recorded names remain unchanged. Its branch is slopmaster2,
as required for upstream WeilConjectures declarations. No mathematical statement changed.
