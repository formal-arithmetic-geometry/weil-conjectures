## Worker report

The module `Sheaf.AlgebraicGeometry.CharZeroConnectedDifferentialTest` states
`AlgebraicGeometry.GeneralLinearGroup.geometricallyConnected_iff_zero_differential_representations_trivial`.
Its only proof is `sorry`. No definitions, helper theorems, or new nodes are needed.
The H2 repair adds the owning definition node `def-wf-lie-algebra-derivation` to the
statement citations and `stmt_deps`, with the citation-only correction recorded below.
The Lean module is byte-for-byte unchanged from returned head 0b8f01e6a734.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| k a characteristic-zero field | `{k : Type u} [Field k] [CharZero k]` |
| H a k-group scheme | `(H : Over (Spec (.of k))) [GrpObj H]` |
| H affine | `[IsAffine H.left]` |
| H finite type | `[LocallyOfFiniteType H.hom] [QuasiCompact H.hom]` |
| Geometrically connected | `GeometricallyConnected H.hom` |
| If and only if | `↔` |
| Every finite-dimensional rational representation | `∀ (m : Type u) [Fintype m] [DecidableEq m] (r : RationalHom H m) [IsMonHom r]` |
| Its differential is zero | `r.differential = 0 →` |
| Every commutative k-algebra A | `∀ (A : Type u) [CommRing A] [Algebra k A]` |
| Every h in H(A) | `(h : AlgebraicGeometry.points H A)` |
| r_A(h) is the identity | `r.points A h = 1` |
| Zero vector space allowed | No `Nonempty m`, `Nontrivial (m → k)` or positive dimension assumption |

The existing representation interface is in basis coordinates: its vector space is `m → k`.
Every finite-dimensional vector space has a finite basis, so choosing one transports its
representation, differential, and triviality to exactly this interface. Conversely each such
finite function space is finite-dimensional. Quantifying over all finite m therefore says
exactly every finite-dimensional rational representation; a basis choice is not a new
hypothesis on the representations. `DecidableEq m` is available classically for each finite
index set. The empty finite index set gives the zero vector space and GL_0, whose point group
is a singleton. Finite-dimensional spaces in any larger universe are likewise isomorphic to
one of these spaces; this formulation uses the established common-universe matrix API.

Test algebras live in the field/scheme universe u, not a smaller independent universe. In
particular the coordinate algebra k[H] and its universal point are included. This is the
usual universe-polymorphic functor-of-points convention of the recorded RationalHom API;
identity on the universal point gives the constant identity morphism, hence identity on
algebra points in any enlarged universe too. All commutative algebras are allowed, including
nonreduced and zero algebras. There is no restriction to rational or geometric field points.

`RationalHom.differential` is the existing Lie algebra homomorphism `Lie H → gl_m`, obtained
by composing `GrpObj.differential r` with `lieAlgebraEquivMatrix`. Its defining source gives
`RationalHom.differential_eq_map_snd`: the value at X is the epsilon coefficient of
`r.points (DualNumber k) (GrpObj.tangentPoint X)`. This is exactly the kernel-of-reduction
differential specified in the node. Matrix endomorphisms identify with End_k(k^m).
`GrpObj.Lie` is the canonical tangent Lie algebra, not an arbitrary Lie algebra or action.
`GeometricallyConnected` uses connected spaces after field extensions; the imported recorded
`geometricallyConnected_iff_connectedSpace_of_isAlgClosed` identifies this with the node's
algebraic-closure test. Connectedness includes nonemptiness.

Dependency declarations read and used:

- def-weil-field: Mathlib `Field`.
- def-sc-group-scheme: `CategoryTheory.GrpObj` in
  `Mathlib.CategoryTheory.Monoidal.Grp`, and `IsMonHom` in
  `Mathlib.CategoryTheory.Monoidal.Mon`. Its record documents the Over(Spec k) specialization.
- def-weil-finite-type-morphism: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact` in their Mathlib morphism modules; their conjunction is
  finite type as the record specifies.
- def-wf-algebraic-representations: recorded module
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Lie`, publicly
  imported. Its `standardRepresentation` specializes the general
  `RationalHom.representation` (also recorded). The latter's own module is
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Representation`; its module
  docstring explicitly identifies an algebraic-group module with `RationalHom`. The actual
  scheme homomorphism and all-algebra points, needed here, are `RationalHom`,
  `RationalHom.points`, and `RationalHom.differential` from the publicly imported upstream
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie`. No definition is copied.
- def-sc-scheme-tangent-space: publicly imported recorded
  `WeilConjectures.AlgebraicGeometry.SchemeTangentSpace`, with `schemeTangentSpace`,
  its additive/module structures and `schemeTangentMap`. The group-specialized canonical
  tangent construction already provided by the RationalHom API is used for this theorem.
- def-sc-dual-numbers: Mathlib `DualNumber` and `DualNumber.eps`, already publicly imported
  by the recorded representation/Lie modules. The differential's source and tangent formula
  use this same dual-number ring.
- def-wf-lie-algebra: Mathlib `LieRing`, `LieAlgebra`, and associative commutator Lie structure;
  the existing differential is a homomorphism of these structures.
- def-wf-lie-algebra-derivation: existing upstream
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket`, primary declaration
  `AlgebraicGeometry.GrpObj.lieEquivTangent`. Its repaired existing:true record also owns
  `GrpObj.Lie`, the additive and module instances, and the canonical bracket, LieRing
  and LieAlgebra instances. Read the full record and upstream declarations: Lie.Basic
  defines `Lie H = Hom(omega H, O)`, and Lie.Bracket identifies it with the kernel of
  dual-number reduction and constructs the commutator bracket. This is precisely the
  domain Lie structure used in `r.differential = 0`. The module is already publicly
  imported transitively through the unchanged recorded representation import.
- def-weil-connected-scheme: Mathlib `ConnectedSpace`, used by `GeometricallyConnected`.

Stated proof dependencies are imported privately: geometric connectedness over an algebraic
closure, the recorded general-linear-group module, the closed-immersion affine criterion,
finite etale components, affine-source separatedness, finite and etale morphisms, the
identity-dual-number unramified criterion, and the etale-algebra product criterion. Cartier
is already available through the public recorded upstream Lie module. The proof nodes
lem-sfb-charzero-lie-detects-factorization,
lem-sfb-finite-group-faithful-regular-matrices, and
lem-sfb-affine-group-lie-tangent-calculus currently have neither a Lean record nor a Mathlib
match, so there is no module to import for them. Their mathematical steps are preserved in
the theorem docstring, for stage 3; none is a missing notion needed to type this statement.

Sources checked: the local Milne PDF, Note 9.50 (connectedness versus finite quotients),
Propositions 10.15 and 10.31, and the node's five proof steps. The docstring carries the whole
proof route: Cartier and identity-subgroup factorization forward; finite etale components,
their faithful regular action, the universal point, and the single-fibre argument backward.

Edge cases checked before writing:

- H = Spec k: geometrically connected; every representation is trivial.
- V = 0: empty m is admitted; matrices and their invertible group are singletons.
- H = G_a or G_m in characteristic zero: zero differential cannot yield a nontrivial
  representation of the connected group.
- Constant Z/2: its sign representation has zero Lie differential and is nontrivial, so
  the right side and geometric connectedness both fail.
- Nonsplit finite etale groups, for example mu_3 over Q: regular representation detects
  the components without assuming k algebraically closed.
- Positive characteristic: the Frobenius character of G_m has zero differential and is
  nontrivial; the explicit CharZero hypothesis excludes this counterexample.
- An empty underlying H is impossible for a group scheme over a field, due to its identity
  section; no extraneous nonemptiness binder is introduced.
- Nonreduced test algebras are retained by the universal A quantifier.

Searches for an existing statement (all no exact match):

1. msearch.py leanfinder: “An affine group scheme of finite type over a characteristic zero
   field is geometrically connected if and only if every finite dimensional rational
   representation with zero differential is trivial”. Eight results concern abstract
   finite-group representation theory and Galois-category connected objects, not this theorem.
2. msearch.py loogle: `"Lie", "Connected"`. Zero hits.
3. msearch.py grep: `connected.*differential|differential.*trivial|zeroDifferential`,
   Mathlib/AlgebraicGeometry. Zero hits.
4. msearch.py leansearch: “An affine group scheme in characteristic zero is connected if
   every rational representation with zero differential is trivial”. Eight hits concern
   finite abstract groups and affine-scheme definitions, not the equivalence.
5. rg in lean/WeilConjectures and lean/Sheaf for connected/differential, zero differential,
   differential/trivial and the exact node id. No existing equivalent theorem. Upstream
   GeneralLinear/Lie provides the invariant-subspace comparison only under algebraic
   closedness, not this all-algebra triviality equivalence over a general field.
6. rg in dag/lean_names_upstream.json for RationalHom and schemeTangentSpace locates the
   existing rational-representation and differential interfaces; read their full signatures
   and docstrings. No fresh representation, Lie or tangent definition is introduced.

No mathematical statement change or STATEMENT-DISPUTED flag is needed. The citation-only
statement correction is recorded to satisfy the stage-2 field rules.

## Second reading by Q89

Reread the original node and final Lean signature clause by clause. The field, characteristic,
affineness, finite type and group structure are all explicit. The right side quantifies over
all finite matrix indices and genuine scheme-group homomorphisms, requires the canonical
Lie differential to vanish, and asserts the identity for all commutative algebra points.
The empty index type retains the zero representation. The geometric connectedness predicate
agrees with the recorded algebraic-closure criterion, including nonemptiness. No mismatches
were found in the mathematical statement. On return, H2 identified the omitted ownership
edge for `GrpObj.Lie` and its structure; that citation and dependency are now explicit. This is the worker's rereading;
independent review is the maintainer's, as specified in the dispatcher brief, which forbids
starting other agents.

Validation: prescribed scompile.py compiled both the sandbox probe and final module path
successfully (23.4 seconds and 8.7 seconds respectively), with no errors or unexpected warnings.
All variables and the universe are explicitly bound, with `set_option autoImplicit false`.

## Repair of returned delivery

H2 (L, independent review of immutable head 0b8f01e6a734): added
`def-wf-lie-algebra-derivation` to `stmt_deps`, cited it in the existing tangent-Lie-algebra
sentence, and documented its recorded declarations above. The Lean remains unchanged, as
authorized by the reviewer. No new declaration or dependency module was introduced.
The sandbox node was compared with current main: before repair its only difference was
the delivered `lean` attachment. The repaired node preserves all current-main fields
except the authorized attachment, citation, dependency and correction audit. The delivery
wrapper performs the rebase and required validation.

## Statement corrected

Old statement (verbatim):

Let $k$ be a field of characteristic zero [def-weil-field], and let $H$ be an affine $k$-group scheme [def-sc-group-scheme] of finite type [def-weil-finite-type-morphism]. For a finite-dimensional rational representation $r:H\to\operatorname{GL}(V)$ [def-wf-algebraic-representations], its differential $dr:\operatorname{Lie}(H)\to\operatorname{End}_k(V)$ is induced on the kernels of reduction of dual-number points; $\operatorname{Lie}(H)$ is the tangent Lie algebra at the identity [def-sc-scheme-tangent-space, def-sc-dual-numbers, def-wf-lie-algebra]. Then $H$ is geometrically connected if and only if every such representation with $dr=0$ is trivial. Geometrically connected means connected after extension to an algebraic closure, with connectedness as in [def-weil-connected-scheme]. Trivial means $r_A(h)=1$ for every commutative $k$-algebra $A$ and every $h\in H(A)$. The zero vector space is allowed.

The only change is adding `[def-wf-lie-algebra-derivation]` within the existing grouped
citation of the tangent Lie algebra. The original statement failed to cite the owning
node of `GrpObj.Lie H` and its canonical Lie structure, although those structures appear
in the elaborated differential. This follows the original Milne source (Note 9.50,
Propositions 10.15 and 10.31, and Cartier 3.23), and the owning definition’s recorded
canonical kernel-of-dual-number-reduction construction. No formula, hypothesis or
conclusion is changed. `statement_change` retains the old text and dependency list.

Citer audit (all nodes whose stmt_deps or proof_deps name this item):

- `lem-sfb-split-charzero-lie-group-integration`: holds true. Only the citation and ownership dependency of the canonical tangent Lie algebra are added; the zero-differential connectedness equivalence is unchanged, so its use in the integration argument still holds.
