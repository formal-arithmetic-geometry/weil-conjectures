## Worker report

Existing attachment; no Lean source is added. The primary declaration is
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationComparison_app_comp_toLowerStar`
in `WeilConjectures.SixFunctors.Etale.Derived.CompactificationRefinementLowerStar`,
lines 194–201. I read this module completely and confirmed the current server source with
`scompile.py --source WeilConjectures.SixFunctors.Etale.Derived.CompactificationRefinementLowerStar`.
The node's `lean.statement` copies its signature verbatim, including its component argument.
The additional existing declarations in `lean.declarations` cover invertibility, the
actual compactification comparison, and the normalization formulas. Nothing outside `lean`
changes in the node. No statement correction, disputed statement, new node, or dependency
module is needed.

Hypotheses and objects, checked individually:

- The finite commutative coefficient ring is `Λ : Type (u + 1)` with `[CommRing Λ]`
  and `[Finite Λ]`; specialize the primary theorem's coefficient category `A` to
  `ModuleCat.{u + 1} Λ`. Its abelian, Grothendieck, monoidal, symmetric, closed,
  monoidal-preadditive, flat-resolution, and small-site-sheafification structures are
  the framework's module-category instances, not extra mathematical assumptions on Λ.
  The primary identity holds more generally; this record uses its stated specialization.
- `T`, `B`, and `h` are the primary theorem's `X Y : Scheme.{u}` and `f : X ⟶ Y`,
  specialized to `[IsProper f]`. Properness is used for the interpretation of both γ's
  as isomorphisms. It is not required by the more general primary identity.
- `D(V_et,Λ)` is exactly `DerivedCategory (Sheaf V.smallEtaleTopology
  (ModuleCat.{u + 1} Λ))`, the `DerivedCategoryModule` abbreviation of
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`, re-exported by the
  dependency's recorded `WeilConjectures.AlgebraicGeometry.DerivedCategories`.
  No bounded subcategory is used. The module universe follows that dependency.
- `c d : Compactification f` have ambient schemes `c.Z`, `d.Z`, proper maps
  `c.g`, `d.g`, open immersions `c.i`, `d.i`, and equalities `c.comm`, `d.comm`.
  The direction of `comm` is `f = i ≫ g`, matching the equality argument of κ.
  Although this structure does not include quasi-compactness of its open immersion,
  proper f is quasi-compact, and `Compactification.quasiCompact_openImmersion`
  supplies it for every c and d. Thus the record covers exactly the compactifications
  in the node when specialized to its proper h.
- The refinement is `r : c.Refinement d` of
  `WeilConjectures.Compactification.RefinementCategory`: `r.hom` is q,
  `r.i_hom : c.i ≫ r.hom = d.i`, and `r.hom_g : r.hom ≫ d.g = c.g`.
  `Compactification.Refinement.isProper` supplies properness of q from these
  factorizations. No different or arbitrary comparison map is substituted.
- The supplied Cartesian square is exactly
  `hcart : IsPullback c.i (𝟙 X) r.hom d.i`. It is retained explicitly, rather
  than inferred for an arbitrary refinement.

Definitions and clauses, checked individually:

- `F_a` and `R_a` are `L((a)^*[A])` and `R((a)_*[A])`, with
  `derivedUpperStarLowerStarAdjunction A a`. For the exact-inverse-image
  convention used in `def-kun-unbounded-exchange`,
  `leftDerivedUpperStarIsoMapDerivedCategory` identifies `L(a*)` with `D(a*)`,
  and `mapDerivedUpperStarLowerStarAdjunction_eq` transports the adjunction.
- `J_c` is `D((c.i)_!open[A])`, using the recorded
  `Etale.openImmersionLowerShriek` from
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
  Its unit is `(derivedOpenImmersionLowerShriekUpperStarAdjunction A c.i).unit`.
- `t_c` is `derivedOpenImmersionLowerShriekToLowerStar A c.i`, defined in
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar` as the
  unit followed by right pushforward of the inverse open-adjunction unit.
  The recorded existing lemma
  `map_derivedOpenImmersionLowerShriekToLowerStar_app_counit` explicitly identifies
  its transpose with the inverse unit, through `L(j*) ≅ D(j*)`. Thus the
  `CategoryTheory.mateEquiv` dependency's prescribed adjunct is used.
- κ is `rightDerivedLowerStarCompHom A c.i c.g f c.comm` (and the analogous
  expression for d). Its definition in `LowerStarProjectionComp` is the conjugate
  of `leftDerivedUpperStarComp` under those adjunctions. It has direction
  `R(c.i)_* ⋙ R(c.g)_* ⟶ Rf_*`, as required. This is the ordinary small-etale
  clause (5), not the pro-etale finite-level specialization currently selected as
  the primary record of `lem-weil-derived-direct-image-composition`.
  `rightDerivedFunctorCompIso'_refinementLowerStarComp_hom_eq` in
  `LowerShriekProjectionRefinement` identifies the resolution-defined compositor
  used in the actual refinement comparison with this conjugate map. This also
  checks the composition normalization; an endpoint isomorphism alone would not do.
- `γ_c.app M` is literally the last two factors on the left of the primary theorem:
  `R((c.g)_*[A]).map ((derivedOpenImmersionLowerShriekToLowerStar A c.i).app M)`
  followed by `(rightDerivedLowerStarCompHom A c.i c.g f c.comm).app M`.
  The right side is exactly `γ_d.app M`. For proper f these are the comparison
  of `def-sp-unbounded-proper-shriek-star-comparison` computed using each c:
  `c.isClosedImmersion_openImmersion` and
  `isIso_derivedOpenImmersionLowerShriekToLowerStar` make the first factor invertible,
  and the canonical compositor is invertible. The chosen-compactification
  construction is the recorded `rightDerivedLowerShriekIsoRightDerivedLowerStar`.
- `b_q` is `(refinementLowerShriekBaseChangeDerivedIso A r hcart).inv`, preceded
  by `leftDerivedUpperStarIsoMapDerivedCategory` when read using L instead of D.
  This is the termwise open base-change mate, with its unit normalization as in
  the dependency's recorded
  `unit_map_derivedOpenImmersionLowerShriekBaseChangeIso` and
  `mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso_mate`. It is not a
  selected isomorphism between the same endpoints.
- `ρ_q` is `rightDerivedLowerShriekOfCompactificationComparison A r hcart` in
  `LowerShriekIndependenceUnbounded`. The recorded formula
  `rightDerivedLowerShriekOfCompactificationComparison_app` in
  `LowerShriekProjectionRefinement`, lines 84–94, expands it into precisely
  `R(r_d)(η_q J_d); R(r_d)R_q(b_q); κ_{r_d,q} J_c`, in application order.
- The primary identity is consequently exactly `ρ_q;γ_c = γ_d` on every M.
  Universal component equality is equivalent to equality of derived natural
  transformations by `CategoryTheory.NatTrans.ext`; all terms are components of
  the displayed canonical natural transformations.
- Invertibility is supplied by the recorded existing instance
  `isIso_rightDerivedLowerShriekOfCompactificationComparison` in
  `LowerShriekIndependenceUnbounded`, lines 185–187, with finite commutative Λ,
  arbitrary f, r, and the same hcart. In particular it applies to the node's proper f.
- For an arbitrary supplied common refinement e, use the primary theorem at
  `q_c : e.Refinement c` and `q_d : e.Refinement d`. Their conclusions are
  `ρ_qc;γ_e = γ_c` and `ρ_qd;γ_e = γ_d`. Since ρ_qd is invertible, the second
  equality is equivalent to `ρ_qd⁻¹;γ_d = γ_e`. Associativity gives
  `(ρ_qc;ρ_qd⁻¹);γ_d = ρ_qc;γ_e = γ_c`. This is the arbitrary-common-refinement
  clause, including its specified order, directly from the same universally
  quantified existing refinement identity and inverse cancellation. No geometric
  comparison theorem or independence assumption is missing from this deduction.
- For the actual `inf(c,d)` comparison, the second equality theorem in
  `CompactificationRefinementLowerStar`,
  `rightDerivedLowerShriekOfCompactificationIso_hom_app_comp_toLowerStar`,
  lines 222–231, states exactly `I_c,d;γ_d = γ_c`. Its `[QuasiCompact f]`
  hypothesis follows from properness. The definition
  `rightDerivedLowerShriekOfCompactificationIso` is literally the `infFst`
  comparison followed by the inverse `infSnd` comparison, with their recorded
  Cartesian squares. `rightDerivedLowerShriekIso` specializes d to
  `HasCompactification.compactification f`. Hence the actual comparison with
  the chosen compactification, not an arbitrary isomorphism, is included.

The dependency records for projection compactification and finite direct-image
composition currently select pro-etale interfaces. I read their signatures and
docstrings (`Scheme.proEtaleRingCompactSupportImage` in
`Sheaf.Paper.ProjectionCompactification`, and `ProEtale.finiteDirectImageComposition`
in `Sheaf.Paper.FiniteDirectImageComposition`). These are not imported or claimed
to be small-etale functors. For this existing attachment the exact small-etale
objects are already defined by the upstream declarations above; no new consumer
module requires a dependency interface repair. Replacing the dependency records
by an etale-only record would discard their other consumers' interfaces, so their
records are left untouched. The underlying compactification datum is the same
`AlgebraicGeometry.Compactification` in both encodings.

Edge cases checked by reading the full source signatures and formulas: identity
refinements; c = d; e = c; the identity compactification `(𝟙 T,h)` for proper h;
the zero derived object; empty schemes and the empty base; the zero ring (no
`Nontrivial` assumption); arbitrary characteristics. No object is required to be
bounded, constructible, or nonzero. No scheme is assumed Noetherian or of finite
type over a prescribed base. Properness gives quasi-compactness without assuming
the base is quasi-compact. The two comparison directions, coarse-to-fine for ρ
and c-to-d through e for I, have both been checked.

Searches actually performed:

- `msearch.py ... leanfinder "Proper refinement comparison of compactifications
  commutes with the canonical derived forget supports map"`: eight topology
  compactification results, including `AbstractCompletion.compare_comp_eq_compare`
  and Stone–Cech statements; none is the etale derived assertion.
- `msearch.py ... loogle "CategoryTheory.Adjunction.comp,
  CategoryTheory.conjugateEquiv"`: twelve generic adjunction/mates results,
  including `conjugateEquiv_associator_hom`; none is the geometric statement.
- `msearch.py ... grep "compactification.*(comparison|[Cc]ompar)|forget.*[Ss]upport"`:
  one irrelevant `LinearAlgebra/Finsupp/Pi.lean` hit.
- `msearch.py ... leansearch "Proper refinement comparison extension by zero
  pushforward agrees with forget supports under derived direct image composition"`:
  eight results, headed by `TopCat.Sheaf.pushforwardForgetIso`, with support and
  ordinary pushforward formulas; no exact Mathlib statement.
- `rg -n` for `lem-sf-proper-refinement-forget-supports`, `comp_toLowerStar`, and
  refinement/forget keywords in `lean/WeilConjectures` and `lean/Sheaf`: located
  the exact upstream `CompactificationRefinementLowerStar` module, and existing
  consumers such as `LowerShriekLowerStarWeil` and
  `Sheaf.SixFunctors.ProjectiveLinePresentedTraceExchange`. No node-id attachment
  existed. Follow-up source searches located the normalization formula in
  `LowerShriekProjectionRefinement` and compositor definition in
  `LowerStarProjectionComp`. These exact existing declarations are recorded.

Validation: there are no delivered Lean files, so no per-file compilation is
required for this existing attachment under brief-stage2 §1 and the worker's
step 2. The mandatory `deliver2.py --no-push` returned `OK (dry run)` for commit
`baef609969b`: preflight passes; no Lean source file is added or compiled.

## Second reading by NA

I performed a separate second pass over the node, the recorded signature, and the
existing source, without delegating (the dispatcher explicitly prohibits other
agents). The primary signature's free context is supplied by the enclosing
`variable` commands; it is an existing declaration, not a new file with unbound
implicits. The coefficient-category specialization and the distinct coefficient
universe were checked against `DerivedCategoryModule`. The node requires proper h;
the source identity works for arbitrary h, so I checked the specialization rather
than silently removing the proper hypothesis. Quasi-compactness of every open
factor follows from proper h even though `Compactification` does not store it.
The Cartesian hypothesis is explicit and is not dropped. The r equations have
the required orientations. I re-read the definitions of t, b, and ρ and the
compositor compatibility lemma: all canonical-map normalizations agree.

I also rechecked the clauses that the primary signature does not print by itself:
invertibility has its own existing instance; the arbitrary e equation follows by
the two displayed substitutions into that universally quantified identity and
inverse cancellation; the inf comparison has its own exact existing theorem.
The chosen-compactification case follows by substituting that compactification
for d in the latter. Accordingly the record lists these declarations separately
and the report does not present the primary signature alone as the whole node.
The empty scheme, zero object, zero ring, and identity refinement require no
additional hypotheses. No mismatch requiring a node change was found.
