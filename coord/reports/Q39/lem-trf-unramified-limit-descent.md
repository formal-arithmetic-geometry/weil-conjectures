## Worker report

The delivery states `AlgebraicGeometry.unramified_limit_descent` in
`Sheaf.TraceFormula.UnramifiedLimitDescent`.  It also defines the canonical
`AlgebraicGeometry.baseChangeHom`, and supplies the §1(B) dependency repair
`AlgebraicGeometry.IsUnramified` in `Sheaf.AlgebraicGeometry.UnramifiedMorphism`.
The theorem proof is intentionally `sorry`; no definition uses postponed data.

The theorem renders the node's hypotheses and conclusion as follows.

- `I : Type u` with `[Preorder I]`, `[IsDirected I (· ≤ ·)]`, and
  `[Nonempty I]` is the nonempty directed index set.
- `D : Iᵒᵖ ⥤ Scheme.{u}` is the inverse system.  The dependent instance
  binders `[∀ i, CompactSpace (D.obj i)]` and
  `[∀ i, QuasiSeparatedSpace (D.obj i)]` say that every stage is qcqs, and
  `[∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]` says every transition is affine.
- `c : Cone D` and `hc : IsLimit c` represent the chosen limit scheme
  `S = c.pt` and its projections.  The recorded declaration
  `AlgebraicGeometry.exists_limit_affine_transition` supplies exactly this
  limit data from the directed affine-transition hypotheses.
- `i₀ : I`, `U₀ V₀ : Scheme.{u}`, and the structure maps
  `u₀ : U₀ ⟶ D.obj (op i₀)` and `v₀ : V₀ ⟶ D.obj (op i₀)`, with the explicit scheme-space instances
  `[CompactSpace U₀] [QuasiSeparatedSpace U₀]` and
  `[CompactSpace V₀] [QuasiSeparatedSpace V₀]`, render qcqs schemes over `S_{i₀}`.
- `g₀ : U₀ ⟶ V₀` and `hg₀ : g₀ ≫ v₀ = u₀` render an `S_{i₀}`-morphism.
- `[LocallyOfFiniteType g₀]` is the node's sole finiteness hypothesis.  No
  flatness, finite presentation, Noetherian, or other hypothesis is added.
- `baseChangeHom u₀ v₀ g₀ t hg₀` is the canonical `pullback.map` from
  `pullback u₀ t` to `pullback v₀ t`, using `g₀`, the identity of the base-change
  scheme, and the identity of `S_{i₀}`.  Thus the hypothesis
  `hg : IsUnramified (baseChangeHom u₀ v₀ g₀ (c.π.app (op i₀)) hg₀)` is the
  unramifiedness of the induced map `g : U → V` over the limit `S`.
- The conclusion `∃ (i : I) (h : i₀ ≤ i), ...` gives a stage at or after `i₀`.
  Its transition `D.map (homOfLE h).op` is the canonical map `S_i ⟶ S_{i₀}`,
  and the displayed `IsUnramified` says the induced `g_i : U_i → V_i` is
  unramified.

The repaired dependency predicate is
`IsUnramified f := LocallyOfFiniteType f ∧
IsOpenImmersion (pullback.diagonal f)`, exactly the dependency node's
unramified definition (Stacks Tags 02G4 and 02GE).  The diagonal uses
Mathlib's canonical fibre product and `pullback.diagonal`; no private copy of a
scheme or fibre product is introduced.

Recorded declarations used are: `AlgebraicGeometry.Scheme` and
`AlgebraicGeometry.Scheme.Hom` (Mathlib); `CategoryTheory.Limits.pullback` and
`pullback.diagonal` (Mathlib); `AlgebraicGeometry.IsAffineHom` (Mathlib);
`AlgebraicGeometry.LocallyOfFiniteType`, `CompactSpace`, and
`QuasiSeparatedSpace` (Mathlib); `AlgebraicGeometry.exists_limit_affine_transition` from
`Sheaf.AlgebraicGeometry.LimitAffineTransition`; and the repaired
`AlgebraicGeometry.IsUnramified` from
`Sheaf.AlgebraicGeometry.UnramifiedMorphism`.

Edge cases checked were a constant inverse system (where `i = i₀` is allowed),
a limit projection with `i = i₀`, empty `U₀` or `V₀` schemes, and arbitrary
(non-flat and non-finitely-presented) locally finite type `g₀`.  The
`[Nonempty I]` binder excludes the empty index set exactly as the node does.
The proof does not add a Noetherian assumption or require finite presentation.

Searches made:

- `msearch.py ... leanfinder "A locally finite type morphism whose base change to an inverse limit of quasi-compact quasi-separated schemes with affine transitions is unramified at a finite stage"`: returned Mathlib formal-unramified and affine-limit factorization declarations, but no eventual-unramified statement.
- `msearch.py ... loogle "AlgebraicGeometry.LocallyOfFiniteType, AlgebraicGeometry.IsOpenImmersion, CategoryTheory.Limits.pullback.diagonal"`: returned the formal-unramified diagonal theorem only, which is a different property.
- `msearch.py ... grep "unramified.*limit|limit.*unramified|IsUnramified" AlgebraicGeometry`: no match.
- `rg` over the project's `lean/Sheaf` and the upstream `WeilConjectures` tree for `unramified_limit_descent`, `IsUnramified`, and `baseChangeHom`: no declaration of this theorem or of the node's combined predicate; unrelated site base-change helpers were excluded.
- `rg` over `dag/nodes` for `lem-trf-unramified-limit-descent`: only this node and its citer were found; the node is not duplicated.

## Second reading by Q39

I reread the copied node and both Lean files after compilation.  The index,
qcqs-stage, affine-transition, chosen-limit, base-scheme, qcqs-source/target,
`S_{i₀}`-morphism, local-finite-type, and limit-unramified hypotheses each have
a corresponding Lean binder.  In this repair the stage and source/target qcqs
conditions are genuine `CompactSpace`/`QuasiSeparatedSpace` instances; the former
identity-morphism binders were removed because they were vacuous.  The conclusion binds both `i` and its witness
`h : i₀ ≤ i`, and its map is the canonical pullback map along the recorded
transition.  The repaired `IsUnramified` expands to exactly locally finite type
plus open-immersion diagonal.  No mismatch was found.  The returned artifact's
missing module, missing lean records, and missing report sections were repaired;
the original node statement and split metadata were otherwise left unchanged.

## Dependency modules

`def-weil-unramified-morphism` had recorded only
`AlgebraicGeometry.LocallyOfFiniteType`, which omits the defining diagonal
condition and therefore cannot render the dependency node's notion.  The
module `Sheaf.AlgebraicGeometry.UnramifiedMorphism` records that notion as the
exact conjunction `LocallyOfFiniteType f ∧ IsOpenImmersion (pullback.diagonal f)`.
Its copied node changes only the `lean` field and includes a note explaining
this §1(B) repair.

## Repair of returned delivery

The maintainer return identified H3 and H8.  H3 is repaired by rendering qcqs
schemes with the genuine Mathlib scheme-space instances `[CompactSpace X]` and
`[QuasiSeparatedSpace X]`: these now occur for every stage and for `U₀` and `V₀`.
The vacuous identity-morphism properties are gone.  The theorem's mathematical
statement and conclusion are unchanged.  H8 is repaired by the theorem docstring's
three numbered proof steps: finite affine covers and local finite type; affine
fibre-product and colimit descriptions; and finite-stage unramified descent followed
by directedness and base change.  Each step names the statement nodes used by the
source proof.
