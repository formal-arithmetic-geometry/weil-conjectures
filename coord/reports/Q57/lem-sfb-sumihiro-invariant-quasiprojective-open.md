## Worker report

The module `Sheaf.AlgebraicGeometry.SumihiroInvariantQuasiprojectiveOpen` states
`AlgebraicGeometry.exists_sumihiro_invariant_quasiprojective_open`, with its entire
proof `sorry`. There are no new definitions or helper theorems. The node changes
only in `lean`; its statement and dependencies are preserved.

Source read: [Brion, Algebraic group actions on normal varieties,
arXiv:1703.09506v3](https://arxiv.org/html/1703.09506v3), Introduction, Theorem 1,
and Section 3.2. The Introduction specifically identifies the smooth connected
affine case as Sumihiro's theorem (1974, Theorem 1 and Lemma 8). The node explicitly
extends the integral-variety case to finite disjoint normal components; it does not
attribute this extension to Milne. Normal finite-type schemes are Noetherian, their
irreducible components are finite and disjoint, and connected G preserves each
component. Thus each point reduces to a normal integral variety; there is no added
integrality hypothesis. No correction or STATEMENT-DISPUTED flag is needed.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Algebraically closed field k | `(k : Type u) [Field k] [IsAlgClosed k]` |
| k-group scheme G | `G : Grp (Over (Spec (.of k)))`; the bundled `Grp` provides precisely `GrpObj G.X` |
| G smooth | `[Smooth G.X.hom]` |
| G affine | `[IsAffine G.X.left]` |
| G finite type over k | `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]` |
| G connected, including nonemptiness | `[ConnectedSpace G.X.left]` |
| X a k-scheme with any G-action | `X : CategoryTheory.Mod (Over (Spec (.of k))) G.X` |
| Action is a scheme morphism satisfying identity and associativity | `Mod.mod` is `ModObj`, with `smul`, `one_smul`, `mul_smul` in Mathlib |
| X separated | `[IsSeparated X.X.hom]` |
| X finite type | `[LocallyOfFiniteType X.X.hom] [QuasiCompact X.X.hom]` |
| Every local ring of X is an integrally closed domain | `hnormal : ∀ p : X.X.left, IsDomain (X.X.left.presheaf.stalk p) ∧ IsIntegrallyClosed (X.X.left.presheaf.stalk p)` |
| Every schematic point x | `(x : X.X.left)`; no rationality/closedness assumption |
| An open subscheme W of X | Existential `W` and `i : W ⟶ X`, with `IsOpenImmersion i.hom.left` |
| It contains x | `x ∈ Set.range i.hom.left` |
| Scheme-level G-invariance | W is a `Mod` object and i is a `Mod.Hom`; the `IsModHom.smul_hom` identity is exactly the action factorization through W |
| W normal | The same pointwise stalk-domain and integral-closure conjunction, quantified over `W.X.left` |
| W separated and finite type over k | `IsSeparated W.X.hom ∧ LocallyOfFiniteType W.X.hom ∧ QuasiCompact W.X.hom` |
| Quasi-projective into some P^n_k, n ≥ 0 | Existential `n : ℕ` and morphism j into `Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (n + 1))) k` |
| Total-degree polynomial grading | This existing definition unfolds to `Proj (MvPolynomial.homogeneousSubmodule ... k)` with the existing graded-algebra structure |
| The immersion is over k | `j ≫ Proj.projectiveSpaceOverAffineToSpec ... k = W.X.hom` |
| Closed immersion into an open subscheme | `IsImmersion j`, whose exact equivalence is Mathlib `IsImmersion.isImmersion_iff_exists` |
| No integrality, smoothness, projectivity, faithfulness, characteristic assumption on X | No corresponding binders or constraints occur |
| Empty X is vacuous | There is no `Nonempty X` binder; the theorem is universally quantified over x |

The choice of an isomorphic open presentation W instead of a literal `X.Opens`
loses nothing: an open immersion identifies W with its open image. A factorization
of the action through an open immersion uniquely induces the identity and
associativity laws on W by cancellation. Hence packaging W and its action as a
`Mod` object does not strengthen the node's invariance clause. Equivariance is
scheme-level, including on nonreduced test schemes, rather than only on k-points.

Dependency declarations read and reused (all full signatures and defining
comments were inspected):

- `def-weil-field`: Mathlib `Algebra.Field.Defs`, `Field`.
- `def-weil-algebraic-closure`: Mathlib `FieldTheory.IsAlgClosed.Basic`,
  `IsAlgClosed` (the precise algebraically-closed-field clause of the recorded match).
- `def-sc-group-scheme`: Mathlib `CategoryTheory.Monoidal.Grp`, `GrpObj` and
  its bundled `Grp`; the scheme specialization was also read in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- The action uses Mathlib `CategoryTheory.Monoidal.Mod`, `ModObj`, `Mod`,
  `Mod.Hom`, `IsModHom`; `CategoryTheory.Monoidal.Cartesian.Mod` gives the
  scheme product action interpretation. No duplicate action definition is introduced.
- `def-sbc-smooth-morphisms`: Mathlib `AlgebraicGeometry.Morphisms.Smooth`, `Smooth`.
- `def-weil-finite-type-morphism`: Mathlib
  `AlgebraicGeometry.Morphisms.FiniteType`, `LocallyOfFiniteType`, and
  `AlgebraicGeometry.Morphisms.QuasiCompact`, `QuasiCompact`, exactly the
  recorded finite-type conjunction.
- `def-weil-affine-spectrum`, `def-pc-scheme`: Mathlib
  `AlgebraicGeometry.Scheme`, `Spec`, `Scheme` and `Scheme.Hom`; affineness is
  existing `IsAffine` in `AlgebraicGeometry.AffineScheme`.
- `def-pc-fibre-product`: Mathlib
  `CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `pullback`; cartesian
  products in `Over (Spec k)` are fibre products over `Spec k`.
- `def-weil-proper-morphism`: Mathlib `AlgebraicGeometry.Morphisms.Proper`
  exposes `IsSeparated` of `AlgebraicGeometry.Morphisms.Separated`.
  No properness hypothesis is introduced.
- `def-weil-pbc-normal-ring`: Mathlib
  `RingTheory.IntegralClosure.IntegrallyClosed`, `IsIntegrallyClosed`, together
  with `IsDomain`, applied to each local ring. This is exactly the node's explicit
  normality clause; no new normality predicate is introduced.
- `def-weil-open-immersion`: Mathlib `AlgebraicGeometry.OpenImmersion`,
  `IsOpenImmersion`.
- `def-weil-closed-immersion`: Mathlib
  `AlgebraicGeometry.Morphisms.ClosedImmersion`, `IsClosedImmersion`, and
  `AlgebraicGeometry.Morphisms.Immersion`, `IsImmersion` and
  `IsImmersion.isImmersion_iff_exists`.
- `def-pc-proj`: Mathlib `AlgebraicGeometry.ProjectiveSpectrum.Scheme`,
  `AlgebraicGeometry.Proj`. Existing
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace` definitions
  `Proj.projectiveSpaceOverAffine` and `Proj.projectiveSpaceOverAffineToSpec`
  specialize it to precisely the polynomial Proj in the node. `ULift (Fin (n+1))`
  has exactly n+1 homogeneous coordinates and places them in the coefficient
  universe. This uses the absolute Proj definition, with no silent identification
  with the separately defined relative `ProjectiveSpace` model.
- `def-weil-connected-scheme`: Mathlib `Topology.Connected.Basic`, `ConnectedSpace`.

The five already-stated proof-dependency modules are imported privately:
`WeilConjectures.AlgebraicGeometry.EffectiveCartier` (divisor dual),
`WeilConjectures.AlgebraicGeometry.Modules.Invertible` (invertible modules),
`WeilConjectures.AlgebraicGeometry.Ample` (`Scheme.Modules.IsAmple`),
`WeilConjectures.AlgebraicGeometry.AmpleImmersionAffineBase`
(`Scheme.Modules.IsAmple.exists_immersion_affine_base`), and
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier`
(`isEffectiveCartierCenter_iff_isInvertible_ker`). The Mathlib proof prerequisite `lem-weil-pbc-affine-opens-basis` uses
`AlgebraicGeometry.Scheme.isBasis_affineOpens` from
`Mathlib.AlgebraicGeometry.AffineScheme`, already available through the public
statement imports. The two proof prerequisites
`lem-sfb-affine-saturation-cartier-boundary` and
`lem-sfb-normal-line-bundle-power-linearization` have no recorded Lean module
in the read snapshot; they are named in the full proof docstring.
No statement object is missing because these are proof prerequisites only.
The future proof must transport the relative projective-space result to the
absolute polynomial Proj, or use its coordinate construction directly.

Edge cases checked before writing: empty X (no x); disconnected normal X (finite
disjoint components, not assumed integral); trivial G and trivial/ineffective
actions; arbitrary characteristic; nonclosed schematic points; n=0 (one homogeneous
coordinate, allowed); and arbitrary field/scheme universe u. No test-object
quantifier or unrelated small universe makes any condition vacuous. Normality
is actual local-ring normality, not an assumption on arbitrary chosen rings.

Searches actually run through `msearch.py Q57 <item>`:

- LeanFinder: `A normal scheme with a connected affine algebraic group action has invariant quasi projective open neighborhoods`:
  8 hits about quasi-affineness, normalization covers and affine covers; no invariant
  quasi-projective-neighborhood statement.
- Loogle: `CategoryTheory.GrpObj, CategoryTheory.MonoidalCategory`: 0 hits.
- grep: `Sumihiro|invariant.*quasi|structure.*Action|class.*Action`:
  25 hits, about abstract group actions and unrelated invariance; no Sumihiro theorem.
- LeanSearch: `A normal variety with a connected algebraic group action has invariant quasi projective open neighborhoods`:
  8 hits, topological group-action neighborhood and fixed-point results; no match.
- Direct `rg` over Mathlib's categorical modules located the exact reusable
  `ModObj`, `Mod`, `Mod.Hom` and `IsModHom` signatures, which were read.
- Direct `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `Sumihiro|sumihiro|MonoidalAction|Action.*Over|MulAction.*Over|structure.*Action`
  found the landed torus specialization and action interfaces, but no theorem
  giving the present general connected affine-group neighborhood.
- Direct `grep -rn` of this node id in `lean/WeilConjectures`: no match.
- Direct name search for `exists_sumihiro_invariant_quasiprojective_open` over
  Mathlib, `WeilConjectures`, `Sheaf` and `dag/lean_names_upstream.json`: no match.
- Existing quasi-projectivity and projective-space source was inspected; the
  absolute Proj helper supplies the requested construction without a new notion.

Validation: the prescribed `scompile.py` compiled both its sandbox probe and the
actual library-path module cleanly (6.4 s and 7.0 s); only the theorem proof is
postponed. No local compiler or global build was run.

## Second reading by Q57

This is a second pass by the author; the dispatch brief forbids starting another
agent and assigns independent review to the maintainer. With the node and final
module open, I rechecked the hypothesis/clause table above against the signature.
The bundled G has the recorded `GrpObj` structure; the X binder supplies an
arbitrary action rather than a representation or a faithful action. Smoothness,
affineness, connectedness and finite type are on G; only separatedness, finite
type and pointwise normality are on X. The result explicitly repeats normality,
separatedness and both finite-type factors on W. The equivariant open immersion
and image membership give an invariant open containing the originally supplied
schematic point. The existential n is a natural number, and its polynomial Proj
has n+1 variables, so P^0 is included. The base equation makes j a k-immersion;
`IsImmersion.isImmersion_iff_exists` gives the exact closed-then-open factorization.
No additional assumptions appear, and empty/disconnected X is not excluded.
No signature mismatch was found and no change was needed on this second pass.
The module has one theorem, one whole-proof sorry, no definitions, explicit
universe/variable binders, public statement imports and private proof imports.
The node copy differs only in `lean`, with its signature copied verbatim.
