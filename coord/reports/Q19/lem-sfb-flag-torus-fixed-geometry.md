## Worker report

The delivery states `AlgebraicGeometry.flag_torus_fixed_geometry` with one postponed proof,
and adds real predicate definitions in `FlagLinearFixedInterfaces`. No result is proved.
The node statement and proof are unchanged. Its statement dependencies gain only
`def-sfb-flag-linear-fixed-interfaces`.

Hypotheses and conclusions, clause by clause:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`.
- `G : Grp (Over (Spec (.of F)))` is the recorded internal group scheme.
  `hG : ReductiveTorusCentralizer.IsReductive G` is the recorded smooth connected affine
  finite-type reductivity predicate, including its geometric unipotent condition.
- The fixed split maximal torus is `iT`, `hT`, `hsplit`; the Borel is `iB`, `hB`.
  Its containment of T is the actual group-scheme map `j` with `hj : j ≫ iB = iT`.
- The quotient Q and right torsor π are any `Q`, `π` with `hπflat`, `hπsurj`, right
  invariance `hπinv`, and the kernel-pair isomorphism `hπtorsor : IsPullback ... π π`.
  This is exactly the presentation supplied by `reductive_borel_pair_structure`.
- The positive roots are `Φplus`; `aB` and `haB` pin its tangent action to conjugation,
  and `hΦplus` identifies it with precisely the nontrivial tangent character weights in B.
  V is not used in this node's assertion; no extra choice of the radical, projection,
  coroots or simple-root base is needed in the Lean binders.
- `Smooth Q.hom ∧ IsProjective Q.hom ∧ ConnectedSpace Q.left` is the first sentence.
- `RankOneRoots.Weyl iT` is the actual scalar-extension normalizer quotient N(F)/T(F).
  `Finite` records finiteness. The `act` conjugation formula pins the Weyl action on T;
  precomposition by `(act w).inv` is exactly χ(n⁻¹tn).
- `aQ` is an internal G-action and `(𝟙 G.X ⊗ₘ π) ≫ aQ.smul = μ[G.X] ≫ π`
  pins it to the canonical left quotient action, not an arbitrary action.
- The existential n chooses E = F^(n+1), which loses no embedding of the nonempty Q
  in a nonzero finite-dimensional representation. `ρ` with `IsMonHom ρ` is an actual
  group-scheme representation into the existing GL scheme. `aP` is the linear action
  on lines, characterized by `IsLinearProjectiveAction` on every algebra, not only
  rational or geometric points. `IsClosedImmersion embedding.left` and its action equality
  are the G-equivariant closed immersion.
- For **every** representative family `nw` with `QuotientGroup.mk (nw w) = w`,
  `Z`, `z` and `e` give the fixed closed subscheme. `Nonempty (IsColimit (Cofan.mk Z e))` presents
  Z as the disjoint union of copies of the monoidal unit Spec F, one for each w;
  thus the scheme is finite and reduced, with no repeated index. The equality
  `e w ≫ z = (nw w).val ≫ π` is e_w = n_w B.
- The `∀ A q` equivalence characterizes that closed subscheme by `IsFixed iT Q aQ A q`.
  `IsFixed` quantifies over every algebra extension A → A' and every S(A')-point;
  this is the scheme fixed subfunctor, including nonreduced algebras.
- `HasTangentWeightBasis` supplies a basis indexed by
  `(inverse Φplus ∪ Φplus) ∖ ((act w).inv ∘ Φplus)`.
  These are exactly Φ minus wΦ⁺, each once. It uses the existing `schemeTangentSpace`,
  its canonical residue-field vector-space structure, and an identification with F
  fixed by the rational point. Each basis vector transforms by its actual torus
  character under postcomposition with the action. Over the algebraically closed
  field, rational points of the split torus detect character identities.
- `cochar : RankOneRoots.Cocharacter T` is an actual G_m → T morphism. Its integer
  `pairing` is pinned by the equality λ;χ = power(pairing χ); positivity is
  `∀ α ∈ Φplus, 0 < pairing α`.
- The final two algebra-point equivalences are equality of the G_m and torus fixed
  subfunctors of the chosen P(E) and of Q. Since the subfunctors are represented
  closed subschemes, this is the asserted equality of fixed subschemes.

Dependency declarations read and reused:

- Mathlib `Field`, `IsAlgClosed` and `CategoryTheory.GrpObj` (including its
  multiplication, identity and inverse diagrams), with the existing bundled `Grp`.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`,
  `AlgebraicGeometry.reductive_borel_pair_structure`: its full signature supplies the
  split torus/Borel inclusions, torsor kernel pair, actual character lattices and
  conjugation actions used here. No dependency interface is replaced.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`,
  `AlgebraicGeometry.IsProjective` and `IsHProjective`: the required H-projective convention.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`.
- Existing `RankOneRoots.Weyl`, `normalizer`, `Character`, `Cocharacter` from
  `Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces`; the existing tangent
  group-character weight spaces from `Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights`.
- Existing `GeneralLinearGroup`, `GeneralLinearGroup.homMulEquiv` from
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`;
  `DiagonalProjectiveAction.space` from the recorded diagonal projective action module;
  `schemeTangentSpace` and its instances from
  `WeilConjectures.AlgebraicGeometry.SchemeTangentSpace`.

All available recorded proof-dependency modules are imported without `public`.
The currently unstated Chevalley line-stabilizer, normalizer/Borel transitivity, and
regular-cocharacter/Borel-description nodes have no module to import; their proof
steps remain fully documented. No missing proof is a hypothesis of the statement.

Edge cases checked: root set empty (G = B = T, Q = Spec F, W trivial), rank-zero
trivial torus, repeated weights in E (the conclusion separates weight *spaces*, not
individual vectors), arbitrary characteristic including p dividing a nonzero exponent,
zero test algebra, nilpotent test algebras, arbitrary representative choices, and the
empty tangent basis. Q cannot be empty because the given torsor is surjective and G
has its identity section. E = F^(n+1) is therefore nonzero without adding a hypothesis.
The projective coordinate convention acts by ρ(g), so it parametrizes lines rather
than using the dual action.

Searches: the prescribed msearch LeanFinder query for flag fixed points returned
root-pairing/Lie-algebra results, none with this scheme statement. Loogle
`AlgebraicGeometry, ModObj, Projectivization` reported an unknown namespace and no
hits. The prescribed Mathlib grep `flag.*fixed|fixed.*flag|projective.*representation`
returned zero hits. LeanSearch for the projective action and tangent character basis
returned the field-valued `Projectivization` action, not a scheme action. LeanFinder
for the same helpers returned elliptic projective point models. The exact helper
name grep returned zero hits. Full query/result records are in the new node's
`mathlib_searches`. `rg` on WeilConjectures, Sheaf and upstream names found no exact
statement or helper; the item-id grep in WeilConjectures returned no declaration.
DAG definition searches and `blueprint_refs.py search` for `projective lines
representation` and `torus fixed` found no matching definition. Existing diagonal
projective action and group-identity tangent weights were read and reused where
applicable. The requested CompactObject example is now withdrawn (module only);
its node's existing-upstream record was read. The delivery follows current module mode.

No statement correction, dependency repair or STATEMENT-DISPUTED flag.

## New nodes

`def-sfb-flag-linear-fixed-interfaces` defines the three pieces of notation above:
fixedness after every algebra extension, the linear projective action on lines with
its actual matrix substitutions, and a tangent character basis at a rational point
with its actual dual-number action. Source: Milne Theorem 4.27, Theorem 13.1,
Lemma 13.51, p.446 before 21.70, and p.447 in 21.73. The definitions have real data
and use existing Proj, GL, internal actions, torus characters and tangent spaces.
Searches found only field-valued projectivization, equalizers of two scheme maps,
and group-identity tangent weights; none supplies these scheme-action interfaces.
The new node cites the existing owning nodes and is a direct statement dependency
of the item.

## Second reading by Q19

A separate second pass by this worker checked the source, node and both files;
no independent agent was started, as the dispatcher brief prohibits delegation.
The maintainer's independent delivery review remains required. This pass checked
that the action on Q is pinned to left multiplication, the projective substitution
is the line convention, all representative choices are quantified, the coproduct
has one Spec F per actual Weyl coset, tangent weights use inverse Weyl
precomposition, and fixedness quantifies over all algebra extensions. No mismatch
requiring a node correction was found. The three helper definitions have no postponed
proof or chosen geometric data.
