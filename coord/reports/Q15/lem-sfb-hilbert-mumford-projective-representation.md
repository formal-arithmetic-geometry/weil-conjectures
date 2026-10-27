## Worker report

The delivery states `AlgebraicGeometry.ProjectiveRepresentation.isStable_iff_all_oneParameterSubgroups_negative`
in `Sheaf.AlgebraicGeometry.HilbertMumfordProjectiveRepresentation` and adds the real-data
coordinate interface `def-sfb-projective-representation-coordinates`. Nothing is proved.
The theorem has the only `sorry`; every helper is an explicit construction or predicate.
The existing item's mathematical statement, proof and proof dependencies are unchanged.
Its statement dependencies gain only the new definition node.

Hypothesis and clause correspondence:

- Algebraically closed field: `(k : Type u) [Field k] [IsAlgClosed k]`.
- Rank r at least two and r-dimensional E: E is finite dimensional and
  `hr : 2 ≤ Module.finrank k E`. Here r is definitionally dim E rather than a redundant
  independent integer. Choosing a basis of E identifies SL(E) with the recorded
  `LinearGroupSchemes.specialLinear k (Module.finrank k E)`. This is a coordinate
  presentation, covering every E and conjugating the quantified cocharacters under
  a change of basis; no property of the representation is restricted.
- Finite-dimensional nonzero V: `[FiniteDimensional k V] [Nontrivial V]`.
  The explicit basis b identifies V with its coordinate vector space. Its lifted index
  has exactly dim V elements. Every finite-dimensional V has such a basis, independently
  of the universe w of its underlying type.
- Rational representation: rho is an actual morphism over Spec k from this SL to the
  existing coordinate GL scheme, with `[IsMonHom ρ]`. It is not a representation merely
  of k-points. The GL source docstring and `GeneralLinearGroup.homMulEquiv` identify
  its points over every algebra with invertible matrices, hence automorphisms of V_R.
- Projective k-scheme: `Y : Over (Spec (.of k))` and `[IsHProjective Y.hom]`, using
  the recorded finite projective-space embedding convention.
- Action and equivariant closed immersion: `A : ModObj ... Y`, `j : Y ⟶ lines V`,
  `[IsClosedImmersion j.left]`, and `hD : IsInduced ρ j A D`.
  The latter coordinate-section identity is imposed on ALL test schemes, including
  nonaffine and nonreduced ones. Since the coordinate sections generate the hyperplane
  line, it determines the projective action and its line lift, not an extra restriction.
  Specifically coordinate forms transform by rho(g^-1). Equality of their pullbacks
  both identifies the image line with rho(g) times the original line and fixes the
  inverse-dual map on that line. Local generators verify this even over nonreduced rings.
- Lines convention and L: `lines V` wraps the existing standard projective scheme in
  Over k, with linear coordinate forms dual to b. `hyperplane j` is exactly the existing
  `ProjectiveSpace.twistRestrict j.left 1`. The induced linearization D is fixed by hD,
  rather than an arbitrary linearized invertible sheaf.
- Semistability: the reused `D.IsSemistable` is nonvanishing of a positive tensor-power
  section invariant on every test scheme. It is part of the reused `D.IsStable`.
- Closed orbit in the semistable locus: the middle clause of `D.IsStable` uses a closed
  subset of the actual geometric base change whose semistable k-points are the orbit.
  Projectivity gives finite type, so this is exactly closedness in the semistable locus.
- Zero-dimensional scheme-theoretic stabilizer: the last clause of `D.IsStable` is
  `topologicalKrullDim (GroupSchemeLinearization.stabilizer A k y) = 0`. The stabilizer
  is the scheme equalizer of orbit and constant maps; no reduction or tangent-space
  condition is substituted.
- k-point and nonzero vector lift: `y : fieldTest k k ⟶ Y`, `v : V`, `hv : v ≠ 0`,
  and `hlift : IsLift b j y v`. The latter says one trivialization of y*L takes every
  restricted coordinate section to b.repr v. This is exactly j(y) = [v]. It is true for
  every chosen nonzero lift by scaling the dual-line trivialization.
- Every nontrivial one-parameter subgroup: the conclusion quantifies over actual
  `lam : multiplicative k ⟶ SL(E)` with `[IsMonHom lam]` and `lam ≠ 1`.
  The 1 in this Hom group is the constant identity group homomorphism.
- Restricted representation and integer components: `restrictedCoaction b ρ lam` is
  explicitly the Laurent universal matrix of rho composed with lam, applied to each
  basis vector and extended by `b.constr`. `HasNegativeWeight` uses the dependency's
  exact `GmRepresentation.weightSpace`, a finite Finsupp decomposition summing to v,
  and a nonzero component at an integer a < 0. The recorded weight-decomposition theorem
  gives existence and uniqueness of these components. The support of nonzero v is finite
  and nonempty, so this condition is exactly `min {a | v_a ≠ 0} < 0`, with the stated sign.
- The result is an iff. There is no characteristic assumption or reducedness, smoothness,
  faithful-representation or separability assumption. Nilpotents in Y and its stabilizer
  are retained by the existing group-scheme stability definition.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field`, from def-weil-field's mathlib_match (no lean record
  is required). Algebraic closure uses `IsAlgClosed`.
- Mathlib.CategoryTheory.Monoidal.Grp and
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs: `GrpObj`, `Grp`, `IsMonHom`;
  the source explicitly specializes the general group-object definition to Over(Spec k).
- Mathlib.AlgebraicGeometry.Scheme: `Scheme` and its morphisms.
- WeilConjectures.AlgebraicGeometry.Morphisms.Projective: `IsHProjective`.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion`.
- Sheaf.AlgebraicGeometry.GmRepresentationWeightBasis: `weightSpace`,
  `weightDecomposition_and_basis`; read its full signature and seven-step proof docstring.
- Sheaf.AlgebraicGeometry.LinearGroupSchemes: `Index`, `specialLinear`, `specialGroup`;
  the full coordinate construction, unique-existence specification and point equivalence
  were read. GL is the existing upstream `GeneralLinearGroup` and `homMulEquiv`.
- Sheaf.AlgebraicGeometry.GroupSchemeLinearization: `act`, `Linearization`, `IsStable`,
  `IsSemistable`, and `stabilizer`; all full definitions were read.
- WeilConjectures.AlgebraicGeometry.ProjectiveSpace and .Twist: existing projective space,
  `twistRestrict`, `twistOneSection`; Modules.PullbackUnit supplies `pullbackΓ`.
- Already stated proof dependencies are imported: AffinePropernessFormalArcTest,
  LinearAlgebra.DvrMatrixSmithPowers, LinearGroupSchemes and GmRepresentationWeightBasis;
  formal-power-series and DVR Mathlib modules are also imported. The orbit-proper theorem
  has no Lean record or current source, so its proof import is left to stage 3/maintenance.

Edge cases checked: Y empty has no y and is included; dim V = 1 and trivial rho give
no stable points (the full positive-dimensional SL stabilizes a point, while all weights
are zero). Trivial cocharacters are excluded. A nontrivial cocharacter in the kernel of
rho has zero weight and correctly obstructs stability. Positive characteristic is
unrestricted, including cocharacters given by pth powers and nonreduced finite
stabilizers. The criterion tests all cocharacters rather than just a fixed diagonal
maximal torus. E and V have independent universes v and w; projective coordinates are
finite lifted index types in k's universe, which excludes no finite-dimensional space.
The zero vector is explicitly excluded; support-minimum is therefore meaningful.

Searches: `msearch.py` LeanFinder query “Hilbert Mumford criterion projective stable point
negative weights every nontrivial one parameter subgroup” returned eight Lie-weight
lemmas, not a GIT theorem (digest 81c0f7776ada1698). Loogle `"Projectivization", "Representation"`
returned zero. Grep `Hilbert.Mumford|HilbertMumford|[Ss]emistable|[Ll]inearization` returned
11 abstract-group homological linearization hits, not projective GIT. LeanSearch query
“Hilbert Mumford criterion geometric invariant theory stable projective point” returned
set-theoretic stabilizer/projectivization lemmas, not this theorem. The three additional
searches for the new notion and their raw result records are in the new node.
Local rg searches in WeilConjectures, Sheaf and DAG nodes found the reused interfaces
above, plus specialized HilbertPlucker.Presentation and PGLLinearization interfaces;
neither handles an arbitrary rational SL representation with a chosen vector lift.
`rg` of the item's exact id in WeilConjectures found no declaration.
`blueprint_refs.py search GIT` returned zero; search linearization returned seven
unrelated blueprint nodes. Ancestor returned None, preserved in the new node.

Sources: the latest blueprint direct-images proof (3), and the item's existing source
and split, were read. MFK is recorded WANTED in the existing item. Morrison was opened
online at https://arxiv.org/pdf/0810.2340: §2.1 explains the induced O(1) linearization;
§2.2 Proposition 1 and its proof identify the minimum-weight sign and cite MFK 2.1.
The project's existing SL and linearization interfaces provide the general scheme form.
No statement fault or correction was needed; no STATEMENT-DISPUTED flag.

Validation: both delivered modules compiled using the prescribed scompile.py against
the live published build, individually and in dependency order. Only the expected theorem
sorry is present. No declaration uses auto-bound variables or file-local notation.

## New nodes

`def-sfb-projective-representation-coordinates` supplies the missing coordinate bridge:
SL of rank dim E, the existing standard projective space viewed as lines in V in a basis,
the existing pulled-back O(1), restricted coordinate sections, the imported matrix entries, the
coordinate characterization of the induced line action, vector lifts, restricted Laurent
coactions and the negative-weight predicate. Its data is explicit, with no postponed
construction. It does not reimplement projective space, stability, GL, SL, weight spaces,
module pullback or line bundles. The source is MFK Chapter 1 §1 and Chapter 2 §1 and
Morrison §2.1--2.2; Mathlib searches find only set-theoretic projectivization. Raw search
records, DAG/upstream search results, source and blueprint provenance are in its JSON.

## Second reading by Q15

Independent second reading by the maintainer reviewer, immutable head 496d8be71fe7. The delivered
section was again the author's own pass. This head removed the bundled copy of Q79's module and node,
since both have now landed. It again carried the four duplicate notions that the reviewer FIX on head
67436661a4c9 had removed; that FIX was lost when the head was returned. I re-applied the same FIX on the
landed `Sheaf.AlgebraicGeometry.ProjectiveRepresentationLinearization`. The landed module is byte-identical
to the copy the earlier fix was compiled against, and the delivered nodes are unchanged since that head.
The reading below is the one from that review and still applies verbatim.

Earlier reading (head 67436661a4c9). The delivered section was again the author's own pass. I read the node, its source place, the seven
stmt_dep records, the three delivered modules, the new coordinates node and the Q79-owned
`def-sfb-projective-representation-linearization` (module byte-identical to Q79's delivered
1c4968b9d3fa copy), plus `GroupSchemeLinearization.{Linearization, IsStable, stabilizer}`,
`LinearGroupSchemes.{Index, specialLinear}`, `GeneralLinearGroup.homMulEquiv`,
`StandardGroupSchemes.multiplicative`, `GmRepresentation.weightSpace` and `PGLLinearization.fieldTest`.

Finding (H4, one definition per notion), repaired by the reviewer. After the repair of the returned
head, the coordinates module imported the owning module but still defined `hyperplane` (j^*O(1) by
`twistRestrict`), `coordinateSection`, `IsInduced` (the same inverse-matrix identity as
`LinearizedEmbedding.coordinates`) and `IsLift` (the same trivialization condition as `IsVectorLift`).
These are second definitions of `line`, `coordinate`, `LinearizedEmbedding` and `IsVectorLift`, and
`line` is built with a different pullback functor (`tensorPullback`). Step 1 of the proof applies
lem-sfb-projective-stability-affine-orbit-proper, which is stated with the owning notions, so stage 3
would have had to transport a linearization and its stability between two models of j^*O(1). The fix
removes the four duplicates. `lines V` is now the abbreviation `ℙ(Index (finrank V); Spec k).asOver (Spec k)`,
the target type of the owning interface. The item takes `D : LinearizedEmbedding (G := specialLinear E) ρ j`,
which bundles the action, the linearization and the coordinate identity, and
`hlift : IsVectorLift (Pi.basisFun k _) j y ⇑(b.repr v)` (the coordinate vector of v lifts j(y), so V keeps
its own universe w), and concludes `D.linearization.IsStable k y ↔ …`. The coordinates node now owns only
`specialLinear`, `lines`, `restrictedCoaction` and `HasNegativeWeight`. Its statement says the line data
are those of the owning node, and its lean.declaration is `HasNegativeWeight`. The stmt_deps are unchanged.

Node statement as a list, with the Lean (after the fix) and the verdict:

1. k algebraically closed: `[Field k] [IsAlgClosed k]`. Correct.
2. r >= 2, dim E = r: `[FiniteDimensional k E]`, `hr : 2 ≤ finrank k E`. Correct.
3. G = SL(E): `specialLinear E = ⟨LinearGroupSchemes.specialLinear k (finrank E)⟩`. This is the coordinate
   presentation and it conjugates cocharacters. It is the same G that Q79's theorem uses. Correct.
4. V ≠ 0 finite dimensional: `[FiniteDimensional k V] [Nontrivial V]`, with basis b over `Index (finrank V)`. Correct.
5. Rational representation: `ρ : SL.X ⟶ GeneralLinearGroup (Index) k`, `[IsMonHom ρ]`, a morphism of group schemes. Correct.
6. Projective Y with G-action: `[IsHProjective Y.hom]`, and `D.action : ModObj G.X Y`. Correct.
7. Equivariant closed immersion j, L = j^*O(1) with the induced linearization: `j : Y ⟶ lines V`,
   `[IsClosedImmersion j.left]`, D. `LinearizedEmbedding.coordinates` is
   D(g,x)(x^*s_i) = Σ_l ρ(g^{-1})_{il} (gx)^*s_l on all test schemes. I checked this: the dual-inverse map
   sends b_i^* to b_i^* ∘ ρ(g)^{-1}. Since the s_i generate, the identity fixes D and implies
   j(gx) = ρ(g)j(x), and every equivariant j has exactly one such D. Correct.
8. Stability (semistable, orbit closed in Y^ss, scheme-theoretic stabilizer of dimension 0):
   `D.linearization.IsStable k y`. It is reused, and the stabilizer is an equalizer, so nilpotents are kept. Correct.
9. y ∈ Y(k) with nonzero lift v: `y : fieldTest k k ⟶ Y`, `hv`, and `IsVectorLift (Pi.basisFun …) j y ⇑(b.repr v)`.
   This gives e : y^*L ≅ O with e(y^*s_i) = b_i^∨(v), which is exactly j(y) = [v]. Every nonzero lift
   satisfies it after rescaling e. Correct.
10. Every nontrivial λ: `∀ lam [IsMonHom lam], lam ≠ 1 → …`. Correct.
11. ν_λ(y) < 0: `HasNegativeWeight (restrictedCoaction b ρ lam) v`. The coaction b_q ↦ Σ_i b_i ⊗ ρ(λ(t))_{iq}
    is the vector (not dual) weight decomposition, and it is unique by the internal sum. Since v ≠ 0, this
    holds exactly when min{a : v_a ≠ 0} < 0, which is the MFK/Morrison sign in the lines convention. Correct.
12. Iff, with no characteristic, reducedness, smoothness or faithfulness assumption. Correct.

Edge cases: Y empty (no y); trivial ρ or dim V = 1 (both sides false); λ in ker ρ (a zero weight obstructs,
as it should); characteristic p, p-power cocharacters and nonreduced stabilizers. Universes: k in u, E in v,
V in w, with index types `ULift.{u} (Fin n)`; the vector lift goes through the coordinate vector, so it adds
no universe restriction. autoImplicit is off.

Compile: one reviewer compile through nt_compile.py --json of ProjectiveRepresentationLinearization
(delivered copy), the fixed ProjectiveRepresentationCoordinates and the fixed
HilbertMumfordProjectiveRepresentation. All were clean; the only `sorry` is the theorem's.

## Repair of returned delivery

The return on immutable head ce191e90b11e identified the duplicate
`AlgebraicGeometry.ProjectiveRepresentation.entry`. I removed the complete local declaration
from `ProjectiveRepresentationCoordinates` and publicly imported
`Sheaf.AlgebraicGeometry.ProjectiveRepresentationLinearization`. The existing generic
`entry` accepts any group scheme and finite index type. Its specialization to SL(E) and
`LinearGroupSchemes.Index (Module.finrank k V)` is exactly the deleted pullback of the GL
coordinate function along `g ≫ ρ`; the existing `IsInduced` formula therefore reuses it
without any change in mathematical content or argument order. It is no longer listed among
the declarations owned by the coordinates module. No declaration was renamed.

The first repair bundled Q79's exact module and owning node because the live lookup
then reported them unavailable. That packaging in head 67436661a4c9 was returned after
Q79's definition node landed. The current repair removes both bundled files and uses the
published module and definition node directly, as detailed below.

The main theorem and its node statement, hypotheses, conclusion and proof route are unchanged
from the returned head. The report's earlier descriptions of matrix entries now refer to the
imported declaration. I rechecked the generic empty-index case and arbitrary scheme-valued
points; the specialization adds no universe equality and loses no nonreduced tests.

Previous-head validation: `scompile.py` compiled all three then-bundled modules separately in
dependency order against the live published build. There were no errors or unexpected
warnings. The coordinates module now imports the sole `entry` implementation, and the
Hilbert--Mumford theorem elaborates with its unchanged signature.

## Repair of returned head 67436661a4c9

The maintainer returned the packet because `def-sfb-projective-representation-linearization`
now exists on `sheaf-dag`. I read the current node, its reviewed Lean record and its full
source, and confirmed availability using the prescribed live `scompile.py --source` lookup.
The landed module is byte-for-byte identical to the copy bundled in the returned packet.
Its `entry` signature and docstring are unchanged, so no consumer interface changes are needed.

I removed `dag/nodes/sec-six-functors-basics/def-sfb-projective-representation-linearization.json`
and `lean/Sheaf/AlgebraicGeometry/ProjectiveRepresentationLinearization.lean` from this
sandbox's delivery packet. They are existing prerequisites, and this delivery no longer
creates or rebinds either of them. The coordinates node retains its statement dependency
on the landed definition node and the coordinates module retains its public import of
`Sheaf.AlgebraicGeometry.ProjectiveRepresentationLinearization`. This reuses the existing
`AlgebraicGeometry.ProjectiveRepresentation.entry` and preserves the preceding duplicate fix.
Only the two Q15 modules and their owning nodes remain in the packet.

Compared with the returned head, the theorem and coordinate definitions are unchanged.
Compared with current `sheaf-dag`, the item still changes only `lean` and gains its
coordinates definition dependency. The new coordinates node is still absent from the base.
The landed linearization node, module and review records are left untouched.

Current repair validation: `scompile.py` compiled the two remaining Q15 modules separately
in dependency order against the live published library, resolving the linearization helper
from the landed source. Both files passed with no errors or unexpected warnings. The
packet contains no source or node copy for the landed prerequisite and no local `entry`
declaration. The main theorem retains its verbatim Lean signature.
