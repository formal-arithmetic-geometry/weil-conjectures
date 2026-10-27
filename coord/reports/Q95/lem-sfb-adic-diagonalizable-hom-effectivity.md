## Worker report

The module `Sheaf.AlgebraicGeometry.AdicDiagonalizableHomEffectivity` states
`AlgebraicGeometry.adic_diagonalizable_hom_effectivity`, with its proof left `sorry`.
It also constructs the quotient bases and their canonical adjacent transition maps.
All three declarations are listed in `lean.declarations`. The helper definitions have
real data: they apply Mathlib's `algSpec` to quotient algebras and `factorₐ`.
There are no new nodes, dependency repairs, or statement corrections.

Source read: Conrad, *Reductive group schemes*, Theorem B.3.2(1), formula (B.3.1),
printed p.288, at https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf.
The split-source instance agrees with the node. The source numbers its bases by
A/m^(n+1); the node numbers them by A/m^n for n ≥ 1. These are the same tower.
The complete accepted seven-step proof is included in the theorem docstring.

Hypothesis and clause correspondence:

- The commutative Noetherian local ring is `(A : Type u) [CommRing A]
  [IsNoetherianRing A] [IsLocalRing A]`.
- Bijectivity of the canonical completion map is
  `[IsAdicComplete (IsLocalRing.maximalIdeal A) A]`, the recorded Mathlib notion.
  `AdicCompletion.of_bijective_iff` in Basic.lean:647 states this equivalence.
- `S = Spec A` is literally `Spec (.of A)` in all group-object categories.
- The finitely generated additive abelian character group is `(M : Type u)
  [AddCommGroup M] [AddGroup.FG M]`.
- The group algebra, its coproduct, counit and antipode are those of the already
  landed `AlgebraicGeometry.ringDiagonalizableGroup A M`. Its definition applies
  `hopfSpec` to `AddMonoidAlgebra A M` with the canonical Mathlib Hopf structure.
  The already landed definition node `def-sfb-ring-diagonalizable-group` is added
  to `stmt_deps`; no duplicate construction is introduced.
- The affine target group is `(G : Grp (Over (Spec (.of A))))` with
  `[IsAffineHom G.X.hom]`. Its finite type is `[LocallyOfFiniteType G.X.hom]`:
  an affine morphism is already quasi-compact (Affine.lean:58), so these are
  exactly affineness and finite type. Over affine Spec A the target is affine,
  and its coordinate algebra is finitely generated over A. No smoothness,
  flatness, or reducedness hypothesis is imposed.
- A group object supplies multiplication, unit and inverse with the group diagrams.
  A morphism in `Grp` preserves multiplication and unit; preservation of the inverse
  follows from the group axioms. Thus these are group homomorphisms, not arbitrary
  scheme morphisms or maps only on rational points.
- `AdicGroupHom.quotientBase A n` is the actual A-algebra spectrum of
  `A ⧸ maximalIdeal A ^ (n+1)`; its structure map is Spec of the quotient map.
  `successorBase A n` is Spec of `Ideal.Quotient.factorₐ A` for
  m^(n+2) ≤ m^(n+1), giving S_n → S_(n+1), with the required direction.
- The family `f` consists of group homomorphisms between the two objects produced
  by `(Over.pullback (quotientBase A n).hom).mapGrp`. Its source is the actual
  base change of D_A(M). The canonical coefficient identification
  A[M] tensor_A A_n = A_n[M] makes this D_(A_n)(M), with the same Hopf operations.
  This is the source's H_(S_n) convention and does not choose a comparison map.
- `hf` is the commuting square
  D_(S_n) → D_(S_(n+1)) → G_(S_(n+1)) = D_(S_n) → G_(S_n) → G_(S_(n+1)).
  Both vertical arrows are the recorded `baseChangeMap` for `successorBase`.
  Since these are the cartesian base-change squares, this equality is precisely
  that the restriction of f_(n+1) equals f_n. Equality of underlying scheme
  morphisms detects equality of the group morphisms. Adjacent compatibility
  implies all-level compatibility by composition.
- The conclusion `∃! g : ringDiagonalizableGroup A M ⟶ G, ∀ n, ...mapGrp.map g = f n`
  expresses surjectivity and injectivity of the specified reduction map together:
  every compatible family has one and only one homomorphism with exactly those
  reductions. Functoriality ensures every g has compatible reductions; the RHS
  is the node's inverse limit as an explicitly compatible family, not a family
  up to unspecified isomorphism.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`,
  full definitions and docstrings at lines 469–480, through `algSpec` and the
  recorded group construction.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the pullback
  conventions and the imported `AlgebraicGeometry.baseChangeMap`. Its complete
  definition/docstring was read in `WeilConjectures.AlgebraicGeometry.PicardFunctor`,
  lines 296–300. It is the actual `pullback.map`; the following
  `isPullback_baseChangeMap` identifies its cartesian square.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (196–198), exactly
  finitely generated ideals; `isNoetherianRing_iff_ideal_fg` was also read.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion` (171–173), the
  subtype of compatible sequences; `IsAdicComplete` (56), Hausdorff and
  precomplete; the equivalence to bijectivity above.
- `Sheaf.AlgebraicGeometry.RingDiagonalizableGroup`:
  `AlgebraicGeometry.ringDiagonalizableGroup`, full declaration and docstring read.
- The proof dependencies already represented by Mathlib are available through
  imports: `AlgebraicGeometry.pullbackSpecIso` (Pullbacks.lean:726),
  `Algebra.TensorProduct.includeLeft`, `includeRight`, `productMap`,
  `productMap_apply_tmul`, `ext` (TensorProduct/Basic.lean and Maps.lean),
  `TensorProduct`, `TensorProduct.lift`, and `TensorProduct.ext'` (LinearAlgebra),
  and `isNoetherian_of_isNoetherianRing_of_finite`,
  `monotone_stabilizes_iff_noetherian`, `set_has_maximal_iff_noetherian`
  (Noetherian/Basic.lean and Defs.lean). Their full signatures/docstrings were read.
  TensorProduct.Maps and Noetherian.Basic are plain proof-only imports.

Edge cases checked before writing:

- M = 0 is allowed and gives the trivial group over A; no positive rank assumption.
- Torsion M, including p-torsion in residue characteristic p, is allowed; the Hopf
  group algebra retains nilpotents, so no accidental smoothness assumption arises.
- If A is a field then m = 0 and every displayed quotient is A; compatibility
  reduces to a constant family and unique lifting is the identity assertion.
- For an Artinian complete local ring, high powers vanish and the tower stabilizes.
- The unit target, arbitrary nonsmooth finite type affine targets, and nonreduced
  complete local rings are admitted. A zero ring is excluded by the standard local
  ring convention, consistent with a maximal ideal and residue field.
- Index zero means exponent one, so no spurious reduction to A/m^0 is added and no
  closed-fibre case is discarded. The finite-support proof includes an empty tensor
  expansion (r = 0) and requires no flatness of the target coordinate ring.
- The universe is explicit and shared by A, M and schemes; finite generation places
  no additional size restriction on the abstract character group (one may take a
  common larger universe). Both auto-implicit options are disabled.

Searches actually run with `msearch.py Q95 lem-sfb-adic-diagonalizable-hom-effectivity`:

- LeanFinder: “Homomorphisms from a split diagonalizable group scheme over a
  complete Noetherian local ring are the inverse limit of their reductions”.
  Eight hits, principally `IsAdicComplete.liftAlgHom`; none is this theorem.
  Its signature was read: it assumes completeness of the target algebra, which
  A[M] does not generally satisfy; it does not establish finite support.
- Loogle: `"HopfAlgebra", "AdicCompletion"`: zero hits.
- Mathlib grep: `diagonalizable|Diagonalizable`, subdirectory AlgebraicGeometry:
  zero hits.
- LeanSearch: “Formal homomorphisms from a split diagonalizable group to an affine
  group scheme algebraize over a complete Noetherian local ring”: eight hits,
  including formal smoothness and `AdicCompletion.liftAlgHom`, no exact match.
- Project and upstream `rg`: `adic.*diagonal|diagonal.*adic`,
  `GroupScheme|groupScheme|Diagonalizable|diagonalizable|HopfAlgebra`, and
  `def .*diagonalizable|def .*Diagonalizable|def relativeSplit` locate the exact
  arbitrary-ring construction `ringDiagonalizableGroup`, as well as field-only
  `diagonalizableGroup` and the relative split torus. Searches for the item id,
  `adic_diagonalizable_hom_effectivity`, and `AdicGroupHom` find no existing theorem
  or conflicting helper name. The consumer CompleteLocalSplitTorusHomLift.lean
  mentions the node only in its proof docstring. The upstream names index was
  searched as well. A DAG search finds the already landed arbitrary-ring definition.

Validation: prescribed `scompile.py` compiled both sandbox and library module modes
in 2.3 seconds each, with no errors or warnings. Only the theorem is postponed.
No statement dispute or node fault was found.

## Second reading by Q95

This is a separate self-review pass by the dispatched worker; no second agent was
started, as the dispatch instructions explicitly prohibit starting other agents.
The maintainer's independent review remains the independent reading.

Reopened the node and final module side by side. Checked the five hypotheses
(commutative, Noetherian, local, complete A; finitely generated abelian M; affine
finite type group G) against the corresponding binders listed above. In particular,
`IsAffineHom` supplies quasi-compactness, so the finite-type binder is exact. Verified
that the existing ring group-algebra construction is used and its node is cited.
Unfolded `algSpec_obj_hom` to check quotientBase's actual map and read `factorₐ` to
check successorBase's direction. Read baseChangeMap's pullback.map definition:
the first composite in hf runs from level n into level n+1 of G, and the second
runs through level n of G, hence precisely records restriction compatibility.
Compared the RHS of the uniqueness assertion with f: it uses the identical
Over.pullback functor, so equality is literal, with no arbitrary map or chosen iso.
The index shift covers exactly n ≥ 1 in the node. No conclusion concerning closed
immersions, flatness, smoothness, or torsion-free characters was accidentally added.
No mismatch was found and no declaration changed during this reading.
