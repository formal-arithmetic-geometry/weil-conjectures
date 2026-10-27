## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SubgroupConjugationIncidenceCriterion`
states `AlgebraicGeometry.subgroup_conjugation_incidence_criterion`, with one whole-proof
`sorry`. It states both clauses of Milne, Algebraic Groups (2017), Lemma 17.32(a),(b),
printed pp.361--362. I read those pages directly from the local PDF with `pdftotext`
(PDF pages 373--374). No new definitions, dependency repairs, or statement corrections
are needed. The node is unchanged outside `lean`.

Hypothesis-by-hypothesis translation:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
  The universe `u` is explicit and arbitrary, with no restriction on characteristic.
- The two group schemes are `(G H : Over (Spec (.of k))) [GrpObj G] [GrpObj H]`.
  These are group objects over the same field, not abstract groups replacing schemes.
- Affineness is `[IsAffine G.left]` and `[IsAffine H.left]`.
- Finite type is `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]` and the same
  two instances for `H.hom`, exactly the dependency's conjunction convention.
- Smoothness and connectedness are `[Smooth G.hom] [ConnectedSpace G.left]` and
  `[Smooth H.hom] [ConnectedSpace H.left]`.
- The inclusion is `(i : H ⟶ G) [IsClosedSubgroupScheme i]`. This supplies a group
  homomorphism and a closed immersion, not merely an inclusion on rational points.
- The separated finite-type quotient is `(X : Over (Spec (.of k)))`, with
  `[IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]`.
- Its projection `(q : G ⟶ X) [Flat q.left] [Surjective q.left]` and `hcoset`
  present precisely the homogeneous quotient in the recorded dependency:
  for every test scheme T, `a ≫ q = b ≫ q` iff `b = a * (h ≫ i)` for some H(T)-point.
  The kernel-pair isomorphism in `exists_homogeneous_fppf_quotient` gives this all-T
  criterion by evaluation; its inverse is `(a,b) ↦ (a,a⁻¹b)`.
- `[ModObj G X]` supplies the scheme action, and `hequiv` is its canonical left-action
  identity `μ[G] ≫ q = lift (fst G G) (snd G G ≫ q) ≫ γ[G,X]`.
  In particular, the fixed-point action is tied to this quotient, rather than arbitrary.
- `hlift` is surjectivity of `g ↦ g ≫ q` on rational points. Together with `hcoset`
  at `T = Spec k`, this is exactly `(G/H)(k) = G(k)/H(k)`.
  The projection properties, coset criterion, equivariance and lifting are explicit
  presentations of the quotient already named by the node, not extra assumptions
  on the subgroup or a restriction to normal subgroups.

Clause-by-clause translation:

- A rational G-point is `a : 𝟙_ (Over (Spec (.of k))) ⟶ G`. Its underlying point is
  `a.left (IsLocalRing.closedPoint k)`. The monoidal unit in this slice is Spec k.
- The set S_H is the existing `Group.conjugatesOfSet` applied to
  `Set.range (fun h : 𝟙_ (Over (Spec (.of k))) ⟶ H ↦ h ≫ i)`.
  By `Group.mem_conjugatesOfSet_iff`, membership means a conjugate of an element
  of that range, equivalently `g * (h ≫ i) * g⁻¹` for some g and h.
- The first conjunct starts `IsProper X.hom →`. Its conclusion is
  `∃ Z : Set G.left, IsClosed Z ∧ ∀ a, a ∈ S_H ↔ |a| ∈ Z`.
  This is equality with Z(k), and does not identify rational points with all points
  of the underlying scheme. No closed-subscheme structure is added to Z.
- The second conjunct assumes `∃ h₀ : ... ⟶ H, {x : ... ⟶ X | (h₀ ≫ i) • x = x}.Finite`.
  This is exactly finiteness of fixed rational cosets, without reducedness or
  scheme-theoretic finiteness of the fixed locus.
- Its conclusion is `∃ V : G.left.Opens, (V : Set G.left).Nonempty ∧ ∀ a,
  |a| ∈ V → a ∈ S_H`. An element of `G.left.Opens` has its canonical open-subscheme
  structure `V.toScheme` and inclusion `V.ι`. A rational point factors through this
  inclusion exactly when its underlying point belongs to V, so the displayed clause
  is precisely `V(k) ⊆ S_H` for a nonempty Zariski open subscheme.
- Properness occurs only inside the first implication; it is absent from the shared
  binders and from the second implication.

Dependency declarations read and reused:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, the algebraic-closedness
  notion explicitly named in the algebraic-closure dependency's `mathlib_match`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj` and the group
  operations on test-point hom sets. The quotient module publicly imports this API.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsClosedSubgroupScheme`, extending `IsSubgroupScheme` and
  including `IsClosedImmersion i.left`. Its source and complete docstring were read.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace` (including nonemptiness).
- `Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousOrbitQuotientGeometry`:
  `AlgebraicGeometry.exists_homogeneous_fppf_quotient`; I read its entire signature,
  proof docstring, and the orbit-stabilizer declaration in the same module.
  It supplies the flat surjective quotient, all-test kernel pair and rational lift.
  Its existing action API is `CategoryTheory.ModObj` and hom-set scalar action.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper` and `IsSeparated`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`; opens carry
  their standard `toScheme`/`ι` open-subscheme construction.
- `Mathlib.Algebra.Group.Subgroup.Basic`: `Group.conjugatesOfSet` and
  `Group.mem_conjugatesOfSet_iff`; no private saturation definition is introduced.

The statement imports its quotient dependency publicly (which publicly exposes the
field, group, smoothness and finite-type APIs), plus Proper, OpenImmersion and the
existing conjugacy-set API. The recorded stated proof modules are plain imports:
AlgebraicSpaceFppfCoveringCalculus, LocallyAlgebraicGroupIdentityComponent,
GeometricallyIrreducibleProduct, FiniteTypeDomainDimensionTrdeg,
FlatCompositeFibreDimensionAtPoint, DimensionLocallyAlgebraic,
SchemeProductDimension, IrreducibleFibreDimensionLowerBound, and the recorded upstream
Spectrum.Prime.Topology module. Noetherian, AlgClosed.Basic and Pullbacks expose the
Mathlib proof leaves. The proof-only node `lem-wf-affine-constructible-open` has no
recorded Lean declaration and therefore contributes no import. It is retained in the
node's proof plan and theorem docstring for stage 3; it is not needed to type this statement.

Edge cases checked before writing:

- H = G: X is a point; every element has a singleton fixed-coset set, and S_H = G(k).
  Both assertions allow Z and V to be the whole underlying scheme.
- H = 1: S_H is the identity. For a positive-dimensional connected group the action
  of the identity fixes all cosets, so the finite-fixed-coset premise is false.
  In dimension zero the smooth connected group over an algebraically closed field
  is trivial and both conclusions still apply.
- Empty groups are not inadvertently quantified as connected: `ConnectedSpace`
  includes nonemptiness, and the group unit already supplies an identity point.
- The fixed fibre may have nilpotents. Only its rational-point set is assumed finite;
  the dimension-zero argument in the proof docstring explicitly allows nonreduced fibres.
- X need not be proper for the second assertion. There is no common properness binder.
- Nonempty V is required as an open subset of the entire scheme, rather than as a
  condition solely on an arbitrary topology imposed on G(k).
- No normality, commutativity, positive dimension, characteristic-zero or extra
  universe equality is imposed.

Searches for an existing statement (all made through the prescribed wrapper):

- LeanFinder: "Conjugation saturation of a closed connected subgroup of an algebraic
  group is closed if its quotient is proper and contains an open if an element has
  finitely many fixed cosets". Eight hits, including `Subgroup.normalCore_isClosed`
  and proper-action subgroup instances; none is the algebraic incidence theorem.
- LeanSearch: "Algebraic group conjugation incidence saturation closed for proper
  homogeneous quotient and dense when some element has finitely many fixed cosets".
  Eight hits, including `Group.conj_mem_conjugatesOfSet`, `MulAction.smul_fixedBy`
  and `Subgroup.quotConjEquiv`; none proves either geometric implication.
- Loogle: `"conjugatesOfSet"`. Twelve hits, including the existing set definition
  and membership lemma used here, but no incidence/closedness/density statement.
- Mathlib grep: `conjugat.*(closed|dense|incidence)|fixed.*coset`. Nine hits, principally
  abstract conjugacy saturation and Sylow fixed cosets; no match.
- Direct `rg` on `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the item id and `conjugation_incidence` found only documentary references in
  BorelConjugationCover. Concept searches in the group-scheme directories found the
  recorded quotient and its consumers, with no existing declaration for this item.
- Read `Group.conjugatesOfSet` and its full membership-lemma signature to reuse the
  existing notion; no auxiliary node or definition was needed.

Validation: the initial scompile run accepted both the sandbox and library module
in approximately 3 seconds each, with one whitespace warning in `γ[G, X]`. I changed
it to `γ[G,X]`; the final clean compile and dry-run results are recorded below.
No STATEMENT-DISPUTED flag or unresolved node fault.

## Second reading by Q74

Fresh in-thread review against the node, the completed file and Milne pp.361--362;
no second agent was started, as instructed by the dispatcher. The maintainer's
independent review remains the independent reading of this delivery.

I checked every shared binder against the node: algebraically closed k; affine finite-type
G and H; smoothness and connectedness of both; a closed subgroup inclusion; a separated
finite-type homogeneous quotient with its genuine left scheme action and rational lifts.
The all-test-scheme criterion prevents replacing the closed subgroup scheme by a mere
rational subgroup, and the equivariance equation prevents using an unrelated action.
I re-expanded `Group.conjugatesOfSet` into conjugation of elements of H(k) and checked
that the underlying-point predicate in each conclusion is applied to G(k)-morphisms.
I checked the scopes of the conjunction and implications: properness belongs only to
closedness; fixed-rational-point finiteness belongs only to the open conclusion. The
open is nonempty on |G| and denotes the canonical open subscheme. No discrepancy was
found. The only change after the first compile was the action-notation whitespace fix.

Final validation: `scompile.py Q74 lem-sfb-subgroup-conjugation-incidence-criterion`
accepted the final file against current server sources in 3.5 seconds with no Lean
warnings or errors. The local compiler reported `OSError(28, 'No space left on device')`;
the wrapper's normal fallback confirmed the clean server compile. The prescribed
`deliver2.py ... --no-push` then printed `OK (dry run): commit 4593544da81 passes the
preflight and compiles; nothing pushed`. Only the module, this report and the item's
lean-only node record were staged. No direct git command or live-source edit was used.

Delivery tool failure: two actual `deliver2.py` push attempts passed compilation and
preflight, then failed with `remote unpack failed: unable to create temporary object
directory` and `(unpacker error)` on the project server. The rejected heads were
`e67f34d8bc8dce89d3656466461962e1d3d7df5a` and
`ab3c0805e506f6e5457456ad788f201e23fe13e2`. No DELIVERED result was printed.
The complete packet remains in the assigned sandbox for a delivery retry after the
server-side temporary-directory failure is repaired. No launcher scripts were edited.
