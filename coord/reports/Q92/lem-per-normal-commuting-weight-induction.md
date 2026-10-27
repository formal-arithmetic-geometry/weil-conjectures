## Worker report

The module `Sheaf.RepresentationTheory.NormalCommutingWeightInduction` states
`Representation.normal_commuting_weight_induction`, with one `sorry` and no definitions.
The node's mathematical statement and dependencies are unchanged. No new nodes or dependency
repairs are needed: intersections of Mathlib eigenspaces, group actions, subgroups, restricted
representations and induced representations already provide all the required notions.

Hypothesis and clause correspondence:

- The algebraically closed characteristic-zero field is `{F : Type u} [Field F]
  [IsAlgClosed F] [CharZero F]`. This uses the algebraically-closed predicate specified in
  `def-weil-algebraic-closure`, not an unnecessary chosen closure of another field.
- The finite group is `{G : Type v} [Group G] [Finite G]`.
- The vector space is `{V : Type w} [AddCommGroup V] [Module F V]`, with
  `[FiniteDimensional F V] [Nontrivial V]`. Its representation is `ρ : Representation F G V`.
  A group representation into endomorphisms consists of invertible operators automatically:
  `ρ g⁻¹` is inverse to `ρ g`. The nonzero/no-proper-invariant-subspace condition is
  `[Representation.IsIrreducible ρ]`, Mathlib's simple-order condition on subrepresentations.
- The normal subgroup is `(A : Subgroup G) [A.Normal]`; the commuting-image condition is
  `hcomm : ∀ a b : A, Commute (ρ a.val) (ρ b.val)`. There is no abelianness assumption on A.
- Characters have type `A →* Fˣ`. The uniquely specified family E satisfies
  `E χ = ⨅ a : A, Module.End.eigenspace (ρ a.val) (χ a : F)`. By
  `Module.End.mem_eigenspace_iff`, this is exactly the node's equation for every a.
  This existentially bound family is fixed by equality with an existing canonical construction;
  the theorem does not choose unspecified data or introduce a competing notion.
- X is always the exact subtype/set `{χ : A →* Fˣ | E χ ≠ ⊥}`. Its `.Finite` and
  `.Nonempty` clauses render finiteness and nonemptiness separately.
- `DirectSum.IsInternal (fun χ : X ↦ E χ.val)` states that the canonical direct-sum inclusion
  is bijective. Since these are F-submodules, the inclusion is F-linear. This is exactly
  the asserted direct-sum decomposition, including uniqueness, rather than spanning alone.
  Classical decidable equality is supplied by `open scoped Classical in`, not a hypothesis.
- `α : MulAction G X` supplies all action laws on X. Its pointwise formula is
  `(α.smul g χ).val a = χ.val (MulAut.conjNormal g⁻¹ a)`.
  `MulAut.conjNormal g⁻¹ a` has underlying element `g⁻¹ * a * g`, so this is exactly
  `(gχ)(a) = χ(g⁻¹ag)`. Characters outside X are not made into extra objects of the action.
- `∀ χ ψ : X, ∃ g : G, α.smul g χ = ψ` is transitivity.
  `(E χ.val).map (ρ g) = E (α.smul g χ).val` is the required equality of transported spaces.
- For each χ in X, `∃ T : Subgroup G` with `∀ g, g ∈ T ↔ α.smul g χ = χ`
  identifies exactly its stabilizer; `A ≤ T` is the asserted subgroup containment.
- `σ : Representation F T (E χ.val)` together with
  `(σ t x : V) = ρ t.val (x : V)` specifies the restricted representation, not an arbitrary
  representation on the same space. `IsIrreducible σ` asserts its irreducibility.
- `e : Representation.Equiv (Representation.ind T.subtype σ) ρ` is an isomorphism of
  G-representations. Its equation on every generator is
  `e (Representation.IndV.mk T.subtype σ g⁻¹ x) = ρ g (x : V)`.
  Mathlib's induced module is the quotient of `F[G] ⊗[F] E χ` by simultaneous left T-action
  on both factors; ambient G acts by right-inverse translation on the basis coordinate.
  Relabel its basis h by the node's basis `[h⁻¹]`. Then its relation
  `(t*h) ⊗ σ(t)x = h ⊗ x` becomes `[h⁻¹t⁻¹] ⊗ σ(t)x = [h⁻¹] ⊗ x`, precisely the
  relation `[gt] ⊗ x = [g] ⊗ σ(t)x`. Its ambient action becomes left translation.
  Thus `IndV.mk g⁻¹ x` is exactly the node's `[g] ⊗ x`; the final equation specifies the
  canonical map on spanning generators, not just an unspecified isomorphism.

Dependency declarations read and used:

- `def-weil-algebraic-closure`: `IsAlgClosed`,
  `Mathlib.FieldTheory.IsAlgClosed.Basic`, lines 57–64, with its equivalence to the root
  definition in the docstring. Also read `IsAlgClosure` at lines 262–268 and the recorded
  `AlgebraicClosure` match; this item only needs the algebraically closed field predicate.
- `lem-sfb-commuting-endomorphisms-common-eigenvector`:
  `Module.End.exists_common_eigenvector_of_commute`,
  `Sheaf.LinearAlgebra.CommutingEndomorphismsCommonEigenvector`; its full signature and
  proof docstring were read, and its module is imported as a proof dependency.
- `lem-per-compatible-generalized-weight-independence`:
  `Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo`,
  `Mathlib.LinearAlgebra.Eigenspace.Pi`, lines 90–92; and
  `iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero`, `Mathlib.LinearAlgebra.DFinsupp`,
  lines 581–583. The Pi module is imported for this proof dependency.
- Additional Mathlib interfaces read: `Representation.IsIrreducible`,
  `Representation.IndV`, `Representation.IndV.mk`, `Representation.ind`,
  `Representation.Equiv`, `Representation.Coinvariants.ker`,
  `MulAut.conjNormal`, and `DirectSum.IsInternal`, with their defining formulas/docstrings.

Sources: read Travaux de Gabber, PDF pages 144–145 (printed pp.138–139), including the
representation lifting immediately before equation (5). It provides context only, exactly as
this node acknowledges; it does not assert this finite-group theorem. Read the current blueprint
`literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.proof.md`.
The inherited Serre reference remains WANTED, not falsely cited as obtained. The module docstring
contains all eight steps of the accepted agent-written proof, with both non-elementary inputs.

Edge cases checked mathematically before finalizing:

- G = A = 1: the sole weight space is V, T = G, and the canonical induction map is identity.
- A = 1 in an arbitrary finite G: again X has one weight, T = G, and σ is ρ.
- A = G with commuting image: there is one character; irreducibility forces its space V
  to be one-dimensional. No assumption that G is abelian was introduced.
- A nonabelian subgroup with scalar image is allowed: a character is invariant under inner
  conjugation because Fˣ is abelian, so A ≤ T remains valid.
- For S3 with A = C3 and the standard two-dimensional representation, the two distinct
  weights form one orbit, T = C3, and induction has the expected two-dimensional source.
- Zero V is excluded exactly as in the node; zero weight spaces are excluded exactly by X.
  Nonfaithful representations and the trivial subgroup are retained. There is no independent
  size restriction: F, G and V have explicitly independent universes u, v and w.

Searches actually performed with `msearch.py Q92 lem-per-normal-commuting-weight-induction`:

- leanfinder: “An irreducible representation of a finite group with commuting normal subgroup
  image decomposes into character eigenspaces and is induced from their stabilizer”. Eight
  hits: invariants/coinvariants and `FDRep.simple_iff_char_is_norm_one`; no whole-statement match.
- loogle: `Representation, "eigenspace"`. Zero hits.
- grep: `weightSpace|imprimitivity|stabilizer`, subdirectory `RepresentationTheory`. Zero hits.
- leansearch: “Clifford theory irreducible representation induced from the stabilizer of a
  character of a normal subgroup”. Eight hits, including `Representation.IndV`, `IndV.mk`,
  `ind`, and induction functors. These supply induction but not the theorem.
- Local `rg` of `weightSpace|character.*[Ee]igen|imprimitivity|normal.*commuting` in
  `lean/WeilConjectures` and `lean/Sheaf`: Lie/group-scheme weight spaces and unrelated
  commuting comparisons only. No finite-group character/stabilizer induction theorem.
- Exact item-id search in `lean/WeilConjectures`: no hits. Exact new declaration-name search
  in Mathlib, `lean/WeilConjectures` and `lean/Sheaf`: no hits.

Validation: server per-file compilation through the prescribed scompile.py; final output below
is reflected in the completed delivery. The first compile exposed field notation on a linear
map; changed it to the fully qualified `Module.End.eigenspace`. A subsequent compile identified
one long docstring line, which was wrapped. No statement correction or disputed statement.

## Second reading by Q92

Worker self-check with the node and module open; the independent maintainer review is separate.
The field, characteristic, finite group, nonzero finite-dimensional vector space, irreducibility,
normality and commuting-image hypotheses each have the explicit binders above. Every conclusion
is present: nonempty finite X, an internal direct sum, the specified transitive action, transport
of spaces, the exact stabilizer, A ≤ T, the irreducible restricted representation, and the
specified equivariant induction isomorphism. Rechecked especially inverse conjugation and the
Mathlib inverse-coordinate convention; the generator equation uses g⁻¹ and so gives rho(g),
not rho(g⁻¹). The existential family, action, subgroup, restriction and isomorphism are each
fully characterized by their displayed formulas. No mathematical mismatch was found; the
namespace and long-line repairs above were the only changes. No independent reviewer is claimed.
