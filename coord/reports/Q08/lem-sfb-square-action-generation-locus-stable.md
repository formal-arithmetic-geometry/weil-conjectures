## Worker report

The module `Sheaf.AlgebraicGeometry.SquareActionGenerationLocusStable` states
`AlgebraicGeometry.square_action_generation_locus_stable`, with its sole proof `sorry`.
It adds no definitions and changes only the item's `lean` field. There are no new
nodes, dependency repairs, statement corrections, or disputed clauses.

Source read: [Guo, Divisors on coherent schemes and homogeneous spaces](https://ningguomath.com/wp-content/uploads/2026/03/amplenew-1.pdf),
March 31, 2026 version, section 5.6 and Lemma 6.3(ii), printed pp.13 and 15.
The item is the explicitly stated smooth, separated, finitely presented specialization.
The first-reading proof in the docstring follows all seven DAG proof steps, including
flat base change from the group local ring rather than a nonflat residue-field base change.

Hypothesis and clause correspondence:

- `S : Scheme.{u}` and `[IsAffine S]` express the affine scheme base, including the empty base.
- `H : Over S` supplies the named structure map `H.hom`. `[GrpObj H]` supplies the
  multiplication, identity and inverse as S-morphisms and their group identities.
  Mathlib's cartesian tensor in `Over S` is precisely the scheme fibre product over S.
- `[Smooth H.hom]`, `[IsSeparated H.hom]`, `[LocallyOfFinitePresentation H.hom]`,
  `[QuasiCompact H.hom]`, `[QuasiSeparated H.hom]` express smoothness, a closed diagonal,
  and finite presentation. The latter three classes are the definition of finite presentation.
- `hH : ∀ s : S, ConnectedSpace (H.hom.fiber s)` means connected, nonempty scheme-theoretic
  fibres over `Spec κ(s)`; it does not substitute connectedness of H or assume S connected.
- `X : Over S` with the separated, locally finitely presented, quasi-compact and
  quasi-separated classes renders the separated finite-presentation structure morphism.
- `[ModObj H X]` is exactly an S-action, with the identity and associativity morphism
  identities. Its action map is `γ[H, X]`; no pointwise action on the bare spaces is assumed.
- `M : X.left.Modules` with `[M.IsInvertible]` is the given invertible structure module.
- `hsquare` quantifies over every `B : Over S` and every `g h : B ⟶ H`. The product
  `g * h` is multiplication in H(B). An invertible `N : B.left.Modules` is existential,
  and `Nonempty (... ≅ ...)` requires only existence of the specified square isomorphism.
  There is no chosen isomorphism, compatibility assumption, properness, commutativity,
  linearization, ampleness, or global-generation hypothesis.
- `(Scheme.Modules.tensorPullback (fst X B).left).obj M` is M_B. Pullback of M along
  `((snd X B ≫ g) • fst X B).left` is canonically τ_g^* M_B: this map is the projection
  X_B → X after the translation τ_g. The recorded tensor-pullback composition comparison
  identifies these expressions, so this uses the actual canonical map rather than an
  arbitrary translation. The other factors use g*h and h in exactly the same way.
  `(Scheme.Modules.tensorPullback (snd X B).left).obj N` is q_B^* N. The tensor grouping
  on the right is `(τ_g^* M_B ⊗ τ_h^* M_B) ⊗ q_B^* N`.
- The conclusion `∃ E : X.left.Opens` with the displayed equality of underlying sets
  names exactly the prescribed union, and asserts its openness without assuming it.
  The union indexes all `n : ℕ` with `0 < n` and all global sections of `M.tensorPow n`.
  Its summands are the recorded `Scheme.Modules.nonvanishingLocus`; no affineness or
  quasi-affineness requirement is attached to these opens.
- `Set.image γ[H,X].left.base ((snd H X).left.base ⁻¹' E) = E` is the image of all
  underlying scheme points of H ×_S E, including points with residue-field extensions.
  It does not replace the scheme product's points by a product of point sets.
- The last conjunct provides `aE : (H ⊗ Over.mk (E.ι ≫ X.hom)).left ⟶ E.toScheme` and
  its equality after composition with `E.ι`. The right side is the original action
  precomposed with H times the open inclusion. This is exactly the stated factorization
  H ×_S E → E of the restricted action.

Recorded statement dependencies used (their complete signatures and docstrings were read):

| DAG notion | Module and declarations |
| --- | --- |
| Schemes, affine and open schemes | `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`; affine API from `WeilConjectures.AlgebraicGeometry.Ample` |
| Smooth morphisms | `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth` |
| Finite presentation | `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `AlgebraicGeometry.LocallyOfFinitePresentation`; quasi-compact/quasi-separated classes |
| Connected schemes | `Mathlib.Topology.Connected.Basic`: `ConnectedSpace` |
| Fibre products | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `CategoryTheory.Limits.pullback`, `.fst`, `.snd`; `Mathlib.CategoryTheory.Monoidal.Cartesian.Over` identifies Over tensors with these pullbacks |
| Residue fields | `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Scheme.Hom.residueFieldMap`; `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber` uses the canonical residue-field point |
| Invertible modules | `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`, `Scheme.Modules.tensorPow` |
| Tensor pullback | `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: publicly imports the actual `Scheme.Modules.tensorPullback` from `WeilConjectures.AlgebraicGeometry.TensorPullback`, and supplies `tensorPullbackSectionComp` |
| Module-sheaf tensors | `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: recorded `SheafOfModules.cochainModulesMonoidal` interface, publicly imported; the existing scheme-module tensor instance comes from `WeilConjectures.AlgebraicGeometry.Modules.Invertible` |
| Nonvanishing opens | `WeilConjectures.AlgebraicGeometry.Ample`: `Scheme.Modules.nonvanishingLocus` (the node also records `Scheme.Modules.IsAmple`, which is not hypothesized) |

Group and action structures are Mathlib's `GrpObj`, `ModObj` and their cartesian Hom
multiplication/action interfaces, not new definitions. Every recorded project proof-dependency
module is included as a plain import; statement dependencies are public imports.

Edge cases checked before writing and again against the final signature:

- If E is empty, the preimage and restricted action source are empty; equality and
  factorization have their intended empty-source meanings. Empty X and empty S are retained.
- The tensor exponent zero is excluded by `0 < n`; exponent one and arbitrary positive
  powers are included. In particular, the zeroth tensor-power unit cannot force E = X.
- For the trivial group the image is E by the unit action. For M = O_X its unit section
  gives E = X, and the conclusion is the original action.
- No reducedness, irreducibility of X, or characteristic restriction is imposed. Nilpotent
  structure is retained, and the nonvanishing predicate uses the maximal-ideal quotient.
- H need not be commutative, and the square relation uses the ordered product g*h.
- The base, group, X and test schemes use the same arbitrary scheme universe u; no smaller
  independent test universe makes the square hypothesis vacuous. No auto-implicit variables
  or universes are permitted by the file settings.

Searches performed with the prescribed `msearch.py Q08 <item>` wrapper:

- LeanFinder: “The positive tensor power section generation locus of a line bundle is
  invariant under a connected smooth group scheme action satisfying the square condition”.
  Eight hits concerned scalar fractions, affine sections and Tilde modules; no theorem
  of this form.
- LeanSearch: “The union of all nonvanishing opens of sections of positive tensor powers
  of an invertible sheaf is stable under a connected group scheme action satisfying the
  square condition”. Eight hits included `Scheme.basicOpen_pow`, open covers and qcqs
  section identities; none states this theorem for module-sheaf sections and scheme actions.
- Loogle: `GrpObj, MulAction` returned zero hits (GrpObj was not recognized by that search
  index). Its actual Mathlib declaration and `ModObj` were subsequently found and read
  directly in `CategoryTheory/Monoidal/Grp.lean`, `Mod.lean`, and `Cartesian/Mod.lean`.
- Wrapper grep: `squareCondition|generationLocus|GroupScheme|Action` in AlgebraicGeometry
  returned unrelated fraction-text matches, and no matching theorem.
- Direct `rg` in Mathlib and the project sources found the existing group/action APIs,
  `nonvanishingLocus`, `tensorPow` and the separate `NormalGroupSquarePower` theorem.
  The latter produces a square identity under normal-base assumptions and does not state
  generation-locus invariance. Searches in `lean/WeilConjectures` for the item id and for
  squareCondition, SquareCondition, generationLocus and PicardAdmissible found no match.
  Searches in `lean/Sheaf` found only unrelated coefficient-complex square-condition code.
  The proposed full declaration name has no existing match.

Validation: the prescribed scompile.py compiled this single file cleanly in both sandbox
and library module modes (34.1 s and 5.6 s reported). The signature is copied verbatim into
`lean.statement`, and the node delta is exactly `lean`. There are no lines over 100 characters.

## Second reading by Q08

Author's second reading; the maintainer supplies the independent review under the dispatch
brief. I reopened the node and completed file and checked all hypotheses and all three
conclusion clauses. The square relation has exactly four translated/original M factors and
one existential invertible base factor. The composite-map expression for τ_g^* M_B uses the
actual action and projection and the existing pullback-composition interface. The union
contains every global section of every strictly positive power, with no affine-open filter.
The image expression uses the preimage under the second scheme projection rather than
pairs of underlying points. The factorization has the correct source H ×_S E and composes
to the original restricted action. Naming E existentially asserts its openness and does not
add an assumption. No mismatches, node corrections or additional declarations were needed.
