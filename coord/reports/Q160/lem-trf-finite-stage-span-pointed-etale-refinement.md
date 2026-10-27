## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteStageSpanPointedEtaleRefinement` states
`AlgebraicGeometry.exists_finiteStage_span_pointed_etale_refinement` with a single
`sorry`. The auxiliary definition `AlgebraicGeometry.Scheme.finiteStageSpanProjection`
is the actual canonical pullback map, constructed by `pullback.map` with identity on
T and the cone projection on the base. It has real data and no postponed proof.
It is a helper of the owning notion, not an independent new definition node.

Sources read: Stacks `more-morphisms.tex`, `lemma-relative-map-approximation-pre`
(Tag 0GDX), especially its supplied-span descent and residue-field paragraphs;
`limits.tex`, `lemma-descend-etale` (Tag 07RP). The reviewed DAG statement gives
precisely the abstract affine-system formulation of those paragraphs, including
the explicit canonical residue comparisons justified by Tag 01JT. No statement
correction, dependency repair or disputed clause is needed.

Hypotheses and notation, clause by clause:

- The nonempty directed index set is `{I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]`. A preorder includes the poset case and
  introduces no meaningful extra mathematical case: its thin category has the
  same directed-system interpretation, as in the recorded affine-chart theorem.
- `D : Iᵒᵖ ⥤ Scheme.{u}` is the inverse diagram, with
  `[∀ i : Iᵒᵖ, IsAffine (D.obj i)]` asserting every stage affine.
  `c : Cone D`, `hc : IsLimit c` give the supplied limit B = c.pt and its
  actual projections `c.π.app (op i)`. No arbitrary limiting identification is chosen.
- `r : I`, `b : c.pt` are the stage and base point. `hres` asserts `IsIso`
  of `(c.π.app (op i)).residueFieldMap b` for every i with r ≤ i, so it is
  specifically the canonical field map, rather than an abstract field equivalence.
- `V P Q : Over (D.obj (op r))` provide each scheme and its structure morphism.
  `hmodels : ∀ T ∈ [V, P, Q], ...` is exactly the conjunction for all three:
  `IsAffine T.left`, `LocallyOfFinitePresentation T.hom`, `QuasiCompact T.hom`,
  `QuasiSeparated T.hom`. The last three are finite presentation in the recorded
  scheme conventions. Membership in this finite list introduces no distinctness
  assumption, and no decidable equality assumption.
- `α : V ⟶ P`, `β : V ⟶ Q` are arbitrary arrows over S_r. Their commuting
  structure triangles are part of Over.Hom; no stage-r étaleness is assumed.
- The pullback of T at the limit is `(Over.pullback (c.π.app (op r))).obj T`,
  whose left scheme is `pullback T.hom (c.π.app (op r))`. At j it is
  `(Over.pullback (D.map (homOfLE hj).op)).obj T`. Its hom is the second projection.
  The arrows are always `((Over.pullback ...).map α).left` and similarly for β.
- `z` is a point of the actual limit pullback of V; `hz` says its second
  projection is b. `hα`, `hβ` say the two limit arrows are étale, and `hαres`,
  `hβres` say the residue maps they induce at z are isomorphisms.

Conclusion, clause by clause:

- `∃ (k : I) (_ : r ≤ k), ∀ (j : I) (_ : k ≤ j) (hj : r ≤ j), ...`
  expresses one eventual bound and every later stage. The explicitly bound hj
  is the forced transitive inequality r ≤ j, used to construct the transition;
  quantifying over its proof does not add a hypothesis or restrict later stages.
- The first conjunct repeats affineness and the three finite-presentation
  conditions for each actual pullback model at j.
- The next two conjuncts assert `Etale` of the two actual pullback arrows.
- Write π_T for `Scheme.finiteStageSpanProjection D c r j hj T`. The next two
  conjuncts read α_j(π_V(z)) = π_P(α_B(z)) and β_j(π_V(z)) = π_Q(β_B(z)).
  Thus the points named z_j, x_j, y_j in the prose are rendered by those terms,
  without any statement-local let or arbitrary chosen point.
- The next three conjuncts are `IsIso (π_V.residueFieldMap z)`,
  `IsIso (π_P.residueFieldMap (α_B z))`, and
  `IsIso (π_Q.residueFieldMap (β_B z))`: all three canonical comparisons.
- The final two conjuncts assert `IsIso` of the stage arrows' residue maps at
  π_V(z). Their source fields are κ(α_j(z_j)) and κ(β_j(z_j)); the two preceding
  point equalities identify those points with x_j and y_j. This is exactly the
  requested κ(x_j) → κ(z_j) and κ(y_j) → κ(z_j), with no field-map substitution.

Recorded statement dependencies used (full signatures/docstrings read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`;
  affineness of objects uses Mathlib's existing `IsAffine`.
- `Mathlib.CategoryTheory.Limits.HasLimits`: the recorded colimit convention's
  dual `CategoryTheory.Limits.Cone` / `IsLimit` and cone projections; their
  definitions in `Cones.lean` and `IsLimit.lean` were also read.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `def-weil-pbc-scheme-conventions` fixes no declaration of its own. Finite
  presentation is spelled out with `QuasiCompact` and `QuasiSeparated` from
  Mathlib's morphism modules, exactly as its lean.note directs.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, `.map`; its actual
  functorial arrows are `CategoryTheory.Over.pullback` from
  `Mathlib.CategoryTheory.Comma.Over.Pullback` (definition read).
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, with the direction and composition lemma read.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.

Proof imports are the recorded existing declarations, with upstream preferred:
`Mathlib.AlgebraicGeometry.Pullbacks` (`pullbackSpecIso`), the qcqs permanence
instances in Mathlib's QuasiCompact/QuasiSeparated/FinitePresentation modules,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
(`locallyOfFinitePresentation_of_comp`),
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Affine` (`isAffineHom_tfae`),
`WeilConjectures.AlgebraicGeometry.EtaleAffineChartDescent`
(`Etale.exists_stage_on_affine_chart`), and
`WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField`
(`Scheme.Pullback.exists_residueField_equiv_ofPointTensor`). Proof-only imports
are not public; imports needed for the statement are public. The docstring
carries all four DAG proof steps and names the nodes each step uses.

Edge cases checked before writing: a singleton index set and identity spans
reduce to the given étale maps and residue hypotheses. The point z rules out
an empty limit V (and therefore an empty base); there is no added nonemptiness
hypothesis on any stage model. Coincident V, P, Q are allowed by list membership.
No injectivity, surjectivity, finite residue extension, Noetherianity, separatedness
or characteristic assumption occurs. In particular κ(z)/κ(b) may be transcendental:
the tensor comparison only uses the canonical κ(p_j(b)) → κ(b) isomorphism.
The index universe is the same u as Scheme.{u}, as required for directed limits;
all binders and the universe are explicit and `autoImplicit` is disabled.

Searches actually run through msearch.py for Q160 and this item:

- leanfinder: "A finite stage span of affine finitely presented schemes eventually
  has etale arrows and canonical residue field isomorphisms if its inverse limit
  does". Eight hits: Scheme.Etale, IsEtale, its composition instances,
  Algebra.Etale.finitePresentation and etale-locus/presentation facts. None is the
  supplied-span theorem.
- loogle: `"residueFieldMap", "IsIso"`. One hit:
  `AlgebraicGeometry.Scheme.instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion`.
  It applies to open immersions, not this affine-limit statement.
- grep, AlgebraicGeometry: `descend.*[Ee]tale|[Ee]tale.*descend|residueFieldMap.*[Ii]so`.
  Three hits: one residue-field over-map instance and the two fpqc descent
  declarations in LocalFlatDescent. No matching eventual pointed-span theorem.
- leansearch: "Eventual pointed etale descent of a supplied finite stage span along
  an affine inverse limit". Eight hits including exists_subalgebra_fg,
  exists_app_map_eq_map_of_isLimit, Scheme.isAffine_of_isLimit, AffineScheme.hasLimits,
  exists_appTop_π_eq_of_isLimit, Scheme.Etale, Profinite.asLimit and the affine cover
  in ExistsHomHomCompEqCompAux. None states the required theorem.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for finite-stage span,
  pointed etale and span/etale patterns found neighbourhood theorems and the
  related FixedFamilyAffineSpanModel, but no matching statement. Searching this
  node id upstream found no occurrence. Searching the final declaration/helper
  names in both roots, Mathlib and dag/lean_names_upstream.json found no collision.

Validation: scompile.py compiled the module in both sandbox and library modes.
The first pass found two style warnings in the helper (a long docstring line
and unnecessary simpa); both were repaired. Final delivery checks are run below
through deliver2.py only. No proof beyond the helper's defining compatibility
identities is supplied; the theorem proof remains sorry.

## Second reading by Q160

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
