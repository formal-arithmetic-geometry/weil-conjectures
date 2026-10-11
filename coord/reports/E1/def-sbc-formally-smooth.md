## Worker report

`Sheaf.AlgebraicGeometry.FormallySmooth` defines
`AlgebraicGeometry.FormallySmooth`, the lifting property in Stacks Project,
More on Morphisms, Definition 37.11.1 (Tag 02H0). The cited source was read
from the published Stacks page and its `more-morphisms.tex` source; the local
`literature/stacks-project/` checkout is absent on this machine.

- A morphism of schemes `f : X -> S` is `(f : X ⟶ S)`, with
  `{X S : Scheme.{u}}`.
- Every pair of affine schemes `T, T'` is quantified by
  `∀ {T T' : Scheme.{u}} ... [IsAffine T] [IsAffine T']`.
- The given first order thickening `i : T -> T'` is
  `(i : T ⟶ T')` with `IsFirstOrderThickening i`. That recorded predicate
  includes closed immersion and square-zero ideal sheaf.
- The map `T' -> S` is `[T'.Over S]`, whose structure morphism is `T' ↘ S`.
  The induced map `T -> S` is `i ≫ (T' ↘ S)`.
- Every map `a : T -> X` over `S` is `(a : T ⟶ X)` with the square equation
  `a ≫ f = i ≫ (T' ↘ S)`.
- The dotted arrow exists as `∃ a' : T' ⟶ X`. Its restriction to `T` is `a`
  by `i ≫ a' = a`, and it is over `S` by `a' ≫ f = T' ↘ S`.

Dependencies: `AlgebraicGeometry.Scheme` and `Scheme.Hom` from
`Mathlib.AlgebraicGeometry.Scheme` (node `def-pc-scheme`);
`Scheme.Over` and its structure map from `Mathlib.AlgebraicGeometry.Over`
(node `def-weil-scheme-over-base`); `AlgebraicGeometry.IsFirstOrderThickening`
from `Sheaf.AlgebraicGeometry.Thickening` (node
`def-sbc-first-order-thickening`). Mathlib's `IsAffine` is from
`Mathlib.AlgebraicGeometry.AffineScheme`.

Edge cases: the quantifier admits the empty affine scheme, the identity
thickening with zero ideal, and arbitrary base schemes without Noetherian,
finite-type, or characteristic restrictions. No uniqueness of the lift is
required. Both affine hypotheses are present as in the node, even though
affineness of `T` follows mathematically from a closed immersion into affine
`T'`.

Searches for an existing declaration:

- `msearch leanfinder` query `formally smooth morphism of schemes lifting
  against affine first order thickenings over a base scheme`: returned
  formally unramified schemes, smooth schemes, and ring-level notions only.
- `msearch loogle` query `AlgebraicGeometry.FormallySmooth,
  Scheme.Hom.FormallySmooth, IsFirstOrderThickening`: no hit; the first name
  is unknown.
- `msearch grep` query `FormallySmooth|formally.smooth|IsFirstOrderThickening`
  in `AlgebraicGeometry`: only ring/stalk formal smoothness appears.
- `rg` in `WeilConjectures/` and `lean/Sheaf/` for `FormallySmooth`:
  only ring-level uses and `FormallySmoothAdic`, no scheme lifting predicate.
- `grep -rn def-sbc-formally-smooth` in `WeilConjectures/`: no match.

Server compile: clean, exit code 0.

## Second reading by E1

Independently checked the node against Stacks Project, More on Morphisms,
Definition 37.11.1 (Tag 02H0), and checked its dependency signatures.

- The schemes `X` and `S` and their morphism `f : X -> S` are
  `{X S : Scheme.{u}} (f : X ⟶ S)`: exact. `Scheme` and its morphisms
  are the Mathlib declarations recorded by `def-pc-scheme`.
- Each pair `T, T'` of affine schemes is quantified by
  `∀ {T T' : Scheme.{u}} ... [IsAffine T] [IsAffine T']`: exact; neither
  affineness condition is silently replaced by one on `X` or `S`.
- The arrow `i : T -> T'` is quantified as `(i : T ⟶ T')`, and
  `IsFirstOrderThickening i` is the hypothesis. The recorded dependency
  defines it as `IsClosedImmersion i ∧ i.ker ^ 2 = ⊥`: exactly the
  first order thickening in the node, including its closed immersion.
- The given structure morphism `T' -> S` is `[T'.Over S]` and
  `T' ↘ S`; the induced structure morphism of `T` is the composite
  `i ≫ (T' ↘ S)`. This matches the recorded `Scheme.Over` declaration.
- Every solid arrow `a : T -> X` making the square commute is
  `∀ (a : T ⟶ X), a ≫ f = i ≫ (T' ↘ S)`: exact. The equation gives
  precisely the required condition that `a` is over `S`.
- The dotted arrow and both triangles are
  `∃ a' : T' ⟶ X, i ≫ a' = a ∧ a' ≫ f = T' ↘ S`: exact. There is no
  uniqueness requirement.

The empty affine scheme and the identity thickening with zero ideal
remain included. The declaration does not require a nonempty scheme,
Noetherianity, finite type, a base field, or a characteristic. `Scheme.{u}`
uses an arbitrary universe level, bound by `universe u`; the source has
no numeric index or degree to restrict. The declaration is a definition
with no `sorry` or proof, and its docstrings identify Tag 02H0 and the
blueprint node. The sandbox node's `lean.statement` matches its signature.

Independent searches: `msearch leanfinder` for scheme morphism,
infinitesimal lifting and square-zero thickening found
`AlgebraicGeometry.FormallyUnramified` and ring-level notions, but no
scheme-level formal smoothness predicate; `msearch loogle` for
`AlgebraicGeometry.FormallySmooth` reported an unknown identifier;
`msearch grep` for `IsFormallySmooth|FormallySmooth|infinitesimal lifting`
found ring-level formal smoothness only. `rg` of Mathlib's algebraic
geometry directory, `WeilConjectures/`, and `lean/Sheaf/` found no
equivalent definition; `FormallySmoothAdic` is a distinct ring notion.
No mismatch was found and no Lean or node text was changed. The module
compiled with `scompile.py` (exit code 0, no warnings).
