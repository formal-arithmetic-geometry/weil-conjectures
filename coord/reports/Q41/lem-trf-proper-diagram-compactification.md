## Worker report

The module `Sheaf.Paper.ProperDiagramCompactification` states
`AlgebraicGeometry.exists_proper_diagram_compactification` for a field `k` and four
separated finite-type `k`-schemes `X`, `Y`, `C`, and `B`. The hypotheses are rendered by
`[X.Over (Spec (.of k))]` and the corresponding `IsSeparated`, `LocallyOfFiniteType`, and
`QuasiCompact` instances for all four structure morphisms. The two correspondence legs
are `c₁ c₂ : C ⟶ X` and `b₁ b₂ : B ⟶ Y`, with their four `IsOver` instances. The proper maps
are `p : X ⟶ Y` and `q : C ⟶ B`, with `[IsProper p]` and `[IsProper q]`; the two commuting
relations are `hp₁ : q ≫ b₁ = c₁ ≫ p` and `hp₂ : q ≫ b₂ = c₂ ≫ p`.

The conclusion existentially supplies `Xstar`, `Ystar`, `Cstar`, and `Bstar`, each with an
over-field instance and proper structure morphism (`IsProper (Xstar ↘ Spec (.of k))`, and
similarly for the other three). It supplies open immersions `uX`, `uY`, `uC`, and `uB`,
with topological density expressed by `DenseRange uX`, `DenseRange uY`, `DenseRange uC`, and
`DenseRange uB`. It supplies proper maps `pstar : Xstar ⟶ Ystar` and
`qstar : Cstar ⟶ Bstar`, and the compactified correspondence maps `c₁star`, `c₂star`,
`b₁star`, and `b₂star`. The eight displayed compatibilities are the witnesses `hX`, `hC`,
`hc₁`, `hc₂`, `hb₁`, `hb₂`, `hleg₁`, and `hleg₂`, using categorical composition `≫`.
Finally, `IsIso (pullback.lift uX p hX)` and `IsIso (pullback.lift uC q hC)` express that the
canonical maps to `Xstar ×_{Ystar} Y` and `Cstar ×_{Bstar} B` are isomorphisms. No Cartesian
condition on the original leg squares and no properness of the original schemes over `k`
is added.

The statement dependencies used are `AlgebraicGeometry.IsProper` from
`Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsOpenImmersion` from
`Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion`, and
`AlgebraicGeometry.ChosenCartesianSquare` from `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`
(the latter is imported as the recorded dependency interface; the theorem uses the canonical
Mathlib pullback map directly). Stated proof-dependency modules are imported as required:
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`,
`Sheaf.Compactification.NagataSketchClosure`, and
`WeilConjectures.Compactification.Dense`.

Edge cases checked: the formulation permits empty schemes and empty correspondence source;
`DenseRange` is the topological density condition and does not impose reducedness or
scheme-theoretic density; `p` and `q` need only be proper as scheme morphisms (the statement
does not add `IsOver` hypotheses); and the pullback clauses use the original maps `p` and `q`
with the displayed commutativity witnesses, so they remain meaningful when either original
leg is an identity or when a scheme is empty.

Searches for an existing declaration: `msearch.py ... leanfinder "simultaneous compactification
of a proper correspondence diagram"` returned only unrelated compact Hausdorff and proper-map
results; `msearch.py ... loogle "IsProper, IsOpenImmersion, DenseRange, pullback.lift"` returned
zero hits (the query name `IsProper` was not recognized); `msearch.py ... grep
"compactification.*correspondence|proper.*diagram" AlgebraicGeometry` returned zero hits; and
`rg` over `WeilConjectures/` and `lean/Sheaf` found no existing declaration of this theorem or
notion. The dependency declarations and their full signatures were read in the recorded Mathlib
and `Sheaf.AlgebraicGeometry.ChosenCartesianSquare` modules.

## Second reading by Q41

I reread the node statement and the completed module. Every original hypothesis is present:
field, four separated finite-type schemes over the field, four `k`-morphism correspondence
legs, proper `p` and `q`, and both equations. Each conclusion clause is matched in order:
proper finite-type compactification schemes, four dense open immersions, proper compactified
vertical maps, four compactified correspondence legs, all five families of compatibility
equations, and the two Cartesian pullback assertions. `DenseRange` is topological density,
and `pullback.lift` is the canonical map determined by each displayed square equation. No
original Cartesian hypothesis or original properness-over-`k` hypothesis was introduced.
The module compiled cleanly with `scompile.py`; the only postponed proof is the required
single `sorry`.

## Maintainer review correction (FIX)

The node works in the category of `k`-schemes: the compactifications are proper `k`-schemes
containing `X,Y,C,B` as dense opens, and the proof forms every closure in a fibre product over
`S = Spec k` (for example `h_X=(j_X,u_Yp):X\to X'\times_SY^*`, which needs `p` to be a `k`-morphism).
The citer lem-trf-proper-direct-image-comparison forms `X^*\times_kX^*` and `c^*=(c_1^*,c_2^*)`.
The delivered conclusion gave `Xstar`, ... arbitrary `Over` instances with no link to `X`, ...:
`uX`, ..., `pstar`, ..., `c₁star`, ... were not required to be `k`-morphisms. So the Lean statement was
weaker than the node, and the citer could not use it. The fix adds the following, and nothing else changes:
- hypotheses `[p.IsOver (Spec (.of k))] [q.IsOver (Spec (.of k))]`. These are needed because, once
  `uX`, `uY` and `pstar` are over `k`, `p ≫ (Y ↘ k) = X ↘ k` follows from `hX`. The citer's proper diagram
  lies over `s = Spec k`.
- in the conclusion, `IsOver (Spec (.of k))` for `uX uY uC uB`, `pstar qstar`, `c₁star c₂star b₁star b₂star`.
  These hold by the node's construction: Nagata compactifications over `S` and projections of
  products over `S`.

A docstring sentence records this convention. The module compiles cleanly with nt_compile.py (the only warning is
`declaration uses sorry`).
