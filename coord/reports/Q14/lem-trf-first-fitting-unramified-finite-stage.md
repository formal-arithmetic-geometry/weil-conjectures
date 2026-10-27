## Worker report

The module `Sheaf.AlgebraicGeometry.FirstFittingUnramifiedFiniteStage` states
`AlgebraicGeometry.firstFitting_unramified_finite_stage`, with its sole proof `sorry`.
It introduces no definitions and changes only the item's `lean` record.

Hypotheses and clause correspondence:

- The nonempty directed set is `{I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]`. Its universe agrees with `Scheme.{u}`,
  as required for these scheme limits; every small directed set can be represented
  in a sufficiently large common universe.
- The inverse system is `D : Iᵒᵖ ⥤ Scheme.{u}`. Affineness is
  `[∀ i, IsAffine (D.obj i)]`, equivalent to an isomorphism with a ring spectrum.
  The affine transition maps are
  `[∀ {i j} (a : i ⟶ j), IsAffineHom (D.map a)]`.
- Each base's finite-type integer structure map is `z i`, with
  `[LocallyOfFiniteType (z i)] [QuasiCompact (z i)]`.
  `Spec (.of (ULift.{u} ℤ))` is the universe-correct spectrum of the integers.
  No compatibility assumptions on these maps are needed: the integer scheme
  structure morphism is unique.
- The specified limit is `L : Cone D` with `hL : IsLimit L`; its underlying
  scheme is `L.pt`, with projection `L.π.app (op c)`.
- The initial index and morphism are `c : I` and `gc : Xc ⟶ D.obj (op c)`.
  Finite presentation is exactly the three binders
  `[LocallyOfFinitePresentation gc] [QuasiCompact gc] [QuasiSeparated gc]`.
- For `hci : c ≤ i`, the base-change morphism `g_i` is
  `pullback.snd gc (D.map (homOfLE hci).op)`. The limit morphism is
  `pullback.snd gc (L.π.app (op c))`.
- The singular closed immersion of any of these morphisms `f` is the recorded
  `Scheme.firstFittingSingularSubscheme f`. Its source is
  `(Scheme.firstFittingIdealSheaf f).subscheme`. Local finite type needed by
  this definition follows from local finite presentation and base change,
  without any new hypothesis.
- The first conjunct quantifies over every `T : Scheme.{u}` and `t : T ⟶ D.obj (op c)`.
  It asserts `Nonempty` of an isomorphism in `Over (pullback gc t)` between
  the base change of the original closed immersion and the first-Fitting closed
  immersion of `pullback.snd gc t`. The former ambient immersion is exactly
  the standard `pullback.map`, with component maps the original singular
  inclusion, `𝟙 T`, and `𝟙 (D.obj (op c))`. The two supplied equalities are
  only witnesses for the commutative squares defining that canonical map.
  Thus the isomorphism preserves the ambient closed subscheme, rather than
  just identifying abstract schemes. Closed immersions are monomorphisms, so
  such an ambient isomorphism is unique. This expresses the canonical
  identification. Specializing `t` to a transition map or a limit projection
  gives both of the node's “in particular” identifications; no separate
  redundant conjunct is necessary.
- The second conjunct quantifies over all `i : I` and `hci : c ≤ i`.
  Its first two clauses, `LocallyOfFiniteType` and `QuasiCompact` of the
  composite singular inclusion, stage morphism, and `z (op i)`, express finite
  type over the integers. The next two clauses, `CompactSpace` and
  `QuasiSeparatedSpace` on that singular scheme, express qcqs. This includes
  `i = c`; the pullback along the identity is canonically the original family.
- The third conjunct is exactly
  `LocallyOfFiniteType (Scheme.firstFittingSingularSubscheme gc ≫ gc)`.
- The last conjunct is an implication, with hypothesis `IsUnramified` of the
  limit singular morphism and conclusion `∃ (d : I) (hcd : c ≤ d),
  IsUnramified` of the stage singular morphism. In particular the limit
  hypothesis does not restrict the preceding base-change and finiteness clauses.
- There are no flatness, smoothness, nodality, or extra finite-presentation
  binders. No condition is imposed on the arbitrary base-change map `t`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `Scheme.Hom`, `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom`;
  `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffine`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`; `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `QuasiSeparated`. The scheme-conventions dependency defines no additional notion.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, and `pullback.map`.
- `WeilConjectures.AlgebraicGeometry.LimitAffineTransition`:
  `exists_limit_affine_transition`; the statement uses its limiting-cone interface.
- `Sheaf.AlgebraicGeometry.FirstFittingSingularSubscheme`:
  `Scheme.isFirstFittingIdealSheaf`, `Scheme.existsUnique_firstFittingIdealSheaf`,
  `Scheme.firstFittingIdealSheaf`, `Scheme.firstFittingSingularSubscheme`, and its
  closed-immersion instance. The dependency's actual full construction is used.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: `IsUnramified`, the exact
  conjunction of local finite type and open-immersion diagonal.

Proof-only imports include `Sheaf.TraceFormula.UnramifiedLimitDescent`
(`unramified_limit_descent`, whose signature and `baseChangeHom` were read) and
`Mathlib.AlgebraicGeometry.Noetherian` for the recorded Noetherianity and
quasi-separatedness leaves. The finite-type composition/base-change and affine-qcqs
Mathlib declarations are available through the statement imports. The two proof
nodes `lem-trf-fitting-ideal-sheaf-pullback` and
`lem-trf-relative-differential-sheaf-base-change` currently have neither a Lean
record nor Mathlib match; they introduce no missing statement notion here, and no
import is possible yet. Their intended applications are recorded in the docstring.

Source read: `divisors.tex`, lemma-base-change-and-fitting-ideal-omega (0C3I),
`limits.tex`, lemma-descend-unramified (0C4W), and `curves.tex`,
lemma-descend-nodal-family (0C5F), especially its final paragraph. The first source
allows arbitrary base change under local finite type; the last paragraph invokes
unramified limit descent precisely on the singular subscheme.

Edge cases checked before writing:

- Empty source and empty bases are allowed; the singular scheme can be empty,
  and the existential stage can be the given initial index.
- The affine line has a rank-one differential sheaf and unit first Fitting
  ideal, so its singular subscheme is empty. No nonemptiness hypothesis excludes it.
- For the nodal affine family `xy = 0`, the first Fitting ideal is `(x,y)` and
  the singular subscheme is the base; this is consistent with both base change
  and the unramified implication.
- A singleton directed system and `d = c` are allowed. There is no strict-index
  condition. Preorders are allowed, with no antisymmetry restriction.
- Non-flat maps `t`, including quotient base changes and the identity, are included.
  All characteristics and the zero ring are allowed.

Searches made (2026-10-24):

- `msearch.py ... leanfinder "First Fitting singular subschemes commute with arbitrary
  base change and unramifiedness descends to a finite stage"`: eight results about
  formally unramified base change, algebra unramified loci, and ring-map properties;
  none states the item.
- `msearch.py ... leansearch "Fitting ideals of relative differentials commute with
  base change and unramifiedness descends along inverse limits"`: eight related
  unramified/base-change results, no exact match.
- `msearch.py ... loogle "AlgebraicGeometry.IsUnramified"`: no result; identifier
  unknown to the Mathlib-only service (it is supplied by the recorded project module).
- `msearch.py ... grep "fittingIdeal|firstFitting|unramified.*limit|limit.*unramified"
  AlgebraicGeometry`: zero Mathlib hits.
- `rg -n 'firstFitting|first_fitting|unramified_limit|lem-trf-first-fitting-unramified-finite-stage'
  lean/WeilConjectures lean/Sheaf`: the existing first-Fitting construction, unramified
  limit descent, nodal special-case theorem, and consumers; none states this full item.
- `grep -rn 'lem-trf-first-fitting-unramified-finite-stage' lean/WeilConjectures`:
  no match. A supplementary search for Fitting base-change statements found only
  a private affine helper in `FiniteJetSmoothGenericFibre`, not this scheme theorem.

No disputed statement, node correction, new node, or dependency repair is needed.
The server `scompile.py` compiled the delivered module in both sandbox and library
module modes with exit code zero and no diagnostics.

## Second reading by Q14

A separate self-review pass reread the node and the completed file; no second
agent was started, in accordance with the dispatcher brief. The first conjunct is
an isomorphism over the ambient scheme and therefore retains the closed immersion;
its quantifier includes both stage and limit maps. The finite-type integer clauses
are conjunctions of local finite type and quasi-compactness, followed by the two
underlying-space qcqs clauses. The limit unramified condition is scoped only over
finite-stage descent. All three finite-presentation hypotheses are present, and
there is no flatness or nodality binder. Every universe and variable is explicit.
No mismatch was found, and no definition was duplicated or corrected.
