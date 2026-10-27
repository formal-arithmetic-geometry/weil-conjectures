## Worker report

Delivery: `Sheaf.AlgebraicGeometry.TraitEtaleBranchPinching`, theorem
`AlgebraicGeometry.exists_trait_etale_branch_pinching`. This is stage 2: its only proof is
`sorry`. No definition or auxiliary theorem is added. The theorem docstring contains all nine
current DAG proof steps, including the maintainer's stage-1 repairs.

The preceding retry diagnosed the Q18 stage-1 review as a completed stage-2 interface. Reading
the live node and Q18 report shows that it was a stage-1 split with no Lean file or Lean record.
This delivery preserves that reviewed statement and proof and supplies the missing statement.
No resplitting or source correction is involved.

Hypotheses, clause by clause:

- The DVR is `R : Type u` with `CommRing`, `IsDomain`, `IsDiscreteValuationRing R`. The base is
  literally `Spec (.of R)`. The fraction field in the generic-fibre clause is `FractionRing R`;
  the residue field mentioned in the prose is the canonical `IsLocalRing.ResidueField R` and
  is not additional data used in the assertion.
- `C B N : Over (Spec (.of R))` specify all three S-schemes. The morphisms `i : B ⟶ C` and
  `j : B ⟶ N` include the required compatibility with those structure maps, rather than adding
  an unrelated absolute morphism.
- Projectivity is `[IsHProjective C.hom]`, exactly the recorded finite projective-space
  convention; flatness is `[Flat C.hom]`; local finite presentation is
  `[LocallyOfFinitePresentation C.hom]`. This is finite presentation here: H-projectivity
  implies properness, hence quasi-compactness and quasi-separatedness. Neither an extra
  separatedness assumption nor a different projectivity convention is introduced.
- `hC` quantifies over every algebraically closed field `Ω : Type u` and every geometric point
  `g : Spec (.of Ω) ⟶ Spec (.of R)`. For its actual scheme pullback, it requires `Nonempty`,
  `IsReduced`, and `Scheme.IsPureDimension ... 1`. For each closed point, expressed by
  `IsClosed ({x} : Set ↥(pullback ...))`, nonsmoothness is nonmembership in the structure
  morphism's `smoothLocus`; `IsGeometricOrdinaryDoublePoint Ω ... x` is exactly the
  maximal-ideal completion of the fibre stalk isomorphic to `Ω[[x,y]]/(xy)`.
- `[IsClosedImmersion i.left]` and `hi` express the branch inclusion and its image lying in
  the relative smooth locus of C/S.
- `[IsFinite B.hom] [Etale B.hom] [IsFinite N.hom] [Etale N.hom]` express finite étale
  S-schemes. `[Etale j.left]` and `[j.left.IsFiniteLocallyFreeOfDegree 2]` express a finite
  étale morphism of constant degree two. The latter existing class contains finiteness,
  flatness, local finite presentation and degree of every residue-field fibre. Those latter
  properties are consequences of finite étaleness; there is no stronger covering assumption.

Conclusions, clause by clause:

- The witnesses `Y : Over (Spec (.of R))`, `a : C ⟶ Y`, `b : N ⟶ Y` are a scheme and its
  S-maps, with `IsPushout i.left j.left a.left b.left` in the category of schemes itself.
  This is the scheme pushout, not merely a pushout in the over category.
- `IsHProjective Y.hom`, `Flat Y.hom`, and the existential local-finite-presentation witness
  `hfp` assert projectivity, flatness and finite presentation, by the same projective-implies-
  quasi-compact-and-quasi-separated observation. The local instance from `hfp` lets the
  statement use the canonical smooth locus of geometric fibres.
- The first quantified conclusion repeats every condition of `hC` for Y. In particular it
  asserts reducedness and pure dimension one, and imposes no connectedness condition.
- `IsFinite a.left ∧ Surjective a.left ∧ IsClosedImmersion b.left` gives the three required
  map properties. `IsPullback i.left j.left a.left b.left` is the cartesian square.
- The existential opens U and V have underlying sets exactly the complements of the two
  closed-immersion images. Their isomorphism e satisfies
  `e.hom ≫ V.ι = U.ι ≫ a.left`, so it is the isomorphism induced by a on complements, not
  an arbitrary isomorphism between unrelated open schemes.
- `Over.pullback` along `Spec.map (algebraMap R (FractionRing R))` supplies the actual generic
  base changes of all four maps; their underlying scheme maps are again `IsPushout`.
- The next clause does the same along every algebraically closed field-valued point g,
  including the nonflat special-fibre base change. The cartesian property is already
  preserved by pullback; this pushout assertion is the additional base-change content.
- The witness `hs : IsPushout ...` includes commutativity and `IsColimit` of the span cocone.
  Its universal property is unique factorization of compatible maps to every scheme in
  `Scheme.{u}`, with no separatedness or S-linearity restriction on the target maps. This
  universal-property clause is represented by that exact standard definition, without a
  redundant extra conjunct restating its consequences.
- For each `V : Y.left.Opens`, `iY` and `jY` are the original maps over Y, with their
  compatibility supplied by `rfl` and `hs.w.symm`. `F := Over.pullback V.ι` gives the actual
  inverse images in B, C, N; `pullback.snd a.left V.ι` and
  `pullback.snd b.left V.ι` are their maps to V. The last `IsPushout` asserts precisely the
  required square in all schemes. These are let-bound canonical constructions from existing
  Mathlib definitions, not sorried helpers or arbitrary maps.

Recorded dependency declarations read and used:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`, `Scheme.Hom.smoothLocus`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.snd`.
- `Mathlib.CategoryTheory.Limits.HasLimits` and
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs`: the standard `IsColimit`,
  `IsPushout` and `IsPullback` interfaces.
- `Mathlib.AlgebraicGeometry.OpenImmersion` and `Restrict`: `IsOpenImmersion`, scheme opens,
  `Opens.toScheme`, `Opens.ι`.
- `Sheaf.AlgebraicGeometry.ProjectiveNodalTower`: `IsGeometricOrdinaryDoublePoint`, whose
  body uses the recorded `AdicCompletion` and `MvPowerSeries (Fin 2)` definitions.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `Scheme.Hom.IsFiniteLocallyFreeOfDegree`, with the actual fibre-degree definition read.
- `Mathlib.CategoryTheory.Comma.Over.Pullback`: `Over.pullback`; `Over.Basic`: `Over.mk`,
  `Over.homMk`. `Mathlib.AlgebraicGeometry.Properties`: `IsReduced`.

The item gains three already-landed statement dependencies to reference those existing notions:
`def-weil-pure-dimension`, `def-trf-projective-nodal-tower` (only its ordinary-double-point
predicate), and `def-pc-finite-locally-free`. No private replacement of a dependency is used.
The broader connected predicates `HasNodalGeometricFibres` and `IsProjectiveNodalCurve` were
read and deliberately not used: they would add connectedness. The proof imports include every
available recorded proof module and the Mathlib proof dependencies. The two proof nodes without
Lean declarations, `lem-sfb-ferrand-scheme-pushout` and `lem-trf-relative-nodal-point-pinching`,
remain explicitly in the proof docstring; neither is needed to type this statement.

Sources read: the current node and each statement dependency with its record; the complete
recorded declarations and their docstrings; Stacks more-morphisms.tex, situation and proposition
`pushout-along-closed-immersion-and-integral`, `lemma-pushout-separated`,
`lemma-pushout-finite-type` (0E25--0E27), and curves.tex `lemma-complete-local-ring-pushout`
and `example-glue-points` (0E36, 0C1J). The projectivity and nodality additions are the agent
trait consequence in the node's source, not claimed to be all verbatim in 0E25.

Edge cases checked: B=N empty gives Y=C and the identity complement isomorphism; the degree-two
condition over empty N is vacuous and does not force nonempty branches. C cannot be empty because
its geometric fibres are explicitly nonempty. Nodes on one component, nodes joining different
components, disconnected fibres, pre-existing nodes away from B, nonsplit double covers,
characteristic two, an arbitrary nonexcellent DVR, and the geometric special fibre are all
retained. No section of the double cover, ordering of its two branches, division by two,
excellence, connectedness or finiteness of normalization is assumed. All fields and schemes use
universe u, as in the recorded geometric-fibre conventions; no independent smaller field universe
can make the fibre hypotheses vacuous.

Searches (all run against the prescribed sources; no exact existing theorem found):

- `msearch.py leanfinder`: “Pinching a projective nodal curve over a discrete valuation ring
  along a finite etale double cover in the smooth locus gives a projective flat nodal curve
  and a cartesian pushout”. Eight hits: Weierstrass minimality, reduction, good reduction,
  nonsingular base change, and Proj's valuative criterion. None states this assertion.
- `msearch.py leansearch`: “A projective flat nodal curve over a discrete valuation ring can be
  pinched along a finite etale double cover in its smooth locus”. Eight hits concern the smooth
  locus, etale morphisms, flatness of projective modules and flat base change. No pinching theorem.
- `msearch.py loogle`: `AlgebraicGeometry.IsPushout, AlgebraicGeometry.Nodal, IsHProjective`.
  Zero hits; the diagnostic is “unknown identifier AlgebraicGeometry.IsPushout” (the correct
  standard namespace is CategoryTheory, whose definition was read directly).
- `msearch.py grep`: `pinching|[Nn]odal|Ferrand`, subdirectory `AlgebraicGeometry`: zero hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the node id, pinching, nodal definitions,
  and the proposed declaration name: no theorem for this node. Hits supplied the existing pure
  dimension, ordinary-double-point, connected nodal-fibre and finite locally free degree APIs.
  The connected APIs were inspected and rejected as too strong for this item.
- DAG searches read `def-trf-projective-nodal-tower`, `def-weil-pure-dimension`,
  `def-pc-finite-locally-free` and their Lean bindings. Existing definitions are used directly;
  no new definition node is necessary.

Validation: every compilation uses the mandated `scompile.py` server wrapper. Initial failures
were pullback coercion/category inference in point and singleton binders; these were repaired by
explicit `C := Scheme.{u}` and point-carrier coercions. No statement change was needed.

## Second reading by Q25

Direct-delivery self-reading under the dispatcher's no-other-agents instruction; this is not
represented as an independent maintainer review. I reread the node, every binder and conjunction,
and the bodies of the notions used. The Q18 PASS concerns the stage-1 split, not a Lean interface.

The first draft used unqualified pullbacks in Type-valued positions; the server diagnosed the
resulting unresolved categories. All those point carriers now explicitly name `Scheme.{u}`.
The closed-point condition is retained (rather than replacing it by a stronger condition at every
point). The output's nodality condition is identical to the input's four fibre clauses.

I checked both `Over.pullback` applications: generic/geometric base changes are over Spec R,
whereas open restriction is over Y itself. The arrow `jY` uses the correct reverse equality
`j.left ≫ b.left = i.left ≫ a.left`; the other arrow is literally i. The two outgoing maps
are the canonical second projections to the open subscheme. Consequently the final clause really
is a scheme pushout of the inverse images of the same V.

I checked that the complement isomorphism commutes with a, that the geometric fibre is the actual
scheme pullback (not the set of field-valued lifts), and that the ordinary-double-point predicate
completes the actual fibre stalk at its maximal ideal. Finite presentation is expressed by local
finite presentation together with projectivity's implied quasi-compactness and quasi-separatedness;
no case is omitted. The finite locally free degree-two interface is equivalent to constant degree
two for an already finite étale map, including the empty target.

No mathematical node fault, disputed statement, hollow definition, extra assumption, source
correction, new node or dependency repair module remains. The only item field changes are `lean`
and the addition of the three existing definition dependencies described above.
