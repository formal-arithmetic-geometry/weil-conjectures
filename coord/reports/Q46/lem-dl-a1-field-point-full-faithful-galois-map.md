## Worker report

The module `Sheaf.AlgebraicGeometry.FundamentalGroup.FieldPointFullFaithfulGaloisMap`
states `AlgebraicGeometry.Scheme.FiniteEtale.field_point_full_faithful_galois_map`,
with one postponed theorem proof and no new definitions. The node's natural-language
statement and dependencies are unchanged. Sources read: Stacks `pione.tex`,
Tags 0BN6 (fully faithful versus surjective), 0BNE (field Galois comparison),
0BQ9 (variance), and 0BQM (normal-scheme application), and the current blueprint
`sec-deligne-laumon-a1/sk-lem-wft-curve-heart/rem-dl-a1-conventions.md`.

Hypothesis and clause correspondence:

- The connected scheme is `{X : Scheme.{u}} [ConnectedSpace X]`. The arbitrary
  field and field point are `(K : Type u) [Field K]` and `a : Spec (.of K) ⟶ X`.
- The chosen separable closure is `Ks`, with `[Field Ks] [Algebra K Ks]`,
  `[IsSepClosed Ks] [Algebra.IsSeparable K Ks]`. These are exactly the two
  components of Mathlib's `IsSepClosure`, by `isSepClosure_iff`; separability
  implies algebraicity. This uses the recorded separable-closure module.
- The algebraic closure of Ks is `Ω`, with `[Field Ω] [Algebra Ks Ω]`,
  `[IsAlgClosed Ω] [Algebra.IsAlgebraic Ks Ω]`, precisely the components of
  `IsAlgClosure Ks Ω` by `isAlgClosure_iff`. `[Algebra K Ω]` and
  `[IsScalarTower K Ks Ω]` specify the induced K-structure. They impose no
  extra field condition or perfectness condition.
- The fully faithful assumption `hfull` states bijectivity of `(pullback a).map`
  for every pair of finite-etale covers P,Q, exactly the stated Hom-set condition.
  It does not assume essential surjectivity of cover pullback.
- `Gal(Ks/K)` is `Aut_K(Ks)` with Mathlib's existing Krull topology.
  The geometric point is `pointOfAlgebra Ω a`. The target group is the existing
  `Aut (fiber (pointOfAlgebra Ω a))`, the finite-etale fibre model explicitly
  used in the node's action and point-set clauses. The recorded FLC comparison
  identifies this model with `Aut (flcFiber _)` from the statement dependency;
  no alternative fibre, topology or fundamental group is defined.
- The first conjunct `∀ σ, ∃! τ : Gal(Ω/K), ...` states unique extension of each
  automorphism, with the displayed equality on all elements of Ks. Neither an
  extension nor its uniqueness is assumed as input.
- The next conjunct gives the precomposition formula for both `j σ` on field
  covers and `q σ` on X-covers, for every extension τ. `q σ` is an actual natural
  automorphism of the existing functor, so naturality, invertibility and the
  homomorphism law are encoded in its type `Gal(Ks/K) →* Aut (fiber _)`.
  The source-side field identification `j` is a topological group isomorphism
  and is characterized by its action on every field cover; it is canonical.
- The displayed equality for `q σ` is exactly the induced fundamental-group
  map applied to `j σ`: `Functor.mapAut` for the whiskering functor restricts a
  natural automorphism to base-changed covers, and `pullbackFiberIso.conjAut`
  transports it to the fibre over X. This is the canonical functorial map on
  automorphism groups. It avoids the smaller `Type u` abstract-model restriction
  of the recorded `fundamentalGroupMap` API while reusing its actual cover
  pullback and natural fibre identification. No arbitrary group homomorphism
  replaces the induced map, and no extra group-model hypotheses are added.
- `Continuous q ∧ Function.Surjective q` is continuity and surjectivity.
  The subsequent `CompactSpace`, `T2Space` and `TotallyDisconnectedSpace`
  conjuncts for both groups express profiniteness; their group structures and
  topological group structures are the existing ones.
- `b P` has domain the geometric fibre of P over X and codomain the Ks-valued
  points of the actual pullback P_K. The equation
  `Spec.map (algebraMap Ks Ω) ≫ (b P t).left ≫ pullback.fst ... = t.left`
  specifies the inverse of scalar extension, rather than an arbitrary bijection.
  The equivariance clause uses the canonical `galoisToAut` on Ks-valued points,
  whose formula is precisely precomposition by `Spec σ`.
- For every `H : Subgroup Gal(Ks/K)` and cover P, the following iff says that all
  H-elements fix all geometric fibre points exactly when they fix all the
  Ks-valued points. It includes arbitrary, nonclosed subgroups.
- For each cover P, `e` is the section restriction equivalence. Its domain is
  `{v : X ⟶ P.obj.left // v ≫ P.obj.hom = 𝟙 X}`; its codomain is the analogous
  type of K-sections of `(pullback a).obj P`. Its first-projection formula
  `(e v).val ≫ pullback.fst ... = a ≫ v.val` specifies base change canonically.
- `d` maps these K-sections bijectively to the subtype of geometric fibre points
  fixed by every σ through q. Its formula is evaluation after `Spec Ω → Spec K`
  followed by the first projection. Thus both of the required bijections and
  their specified maps are present; mere equal cardinalities are not used.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`:
  `IsSepClosure.exists_intermediateField_mem` and its imported `IsSepClosure`,
  `IsSepClosed`, `isSepClosure_iff`. The theorem uses the underlying closure
  conditions; it does not insert a private separable-closure definition.
- `Mathlib.FieldTheory.IsAlgClosed.Basic` / `.AlgebraicClosure`: `IsAlgClosure`,
  `IsAlgClosed`, `isAlgClosure_iff`; arbitrary chosen closures are allowed.
- `WeilConjectures.AlgebraicGeometry.GaloisCategories`: `Scheme.FLC`, with the
  node's existing `Scheme.FiniteEtale` and `FiniteEtale.fiber` from
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale`.
- `Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber`: `Scheme.flcFiber`, the
  recorded stalk model; its finite-etale counterpart and the fibre comparison
  are re-used, not redeclared.
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.GaloisAction`:
  `pointOfAlgebra`, `galoisToAut`, `galoisToAut_hom_app_left`.
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction`:
  `pullbackFiberIso`, its first-projection formula, and the recorded
  `fundamentalGroupMap`, `fundamentalGroupMap_smul`,
  `continuous_fundamentalGroupMap` signatures. The actual pullback functor is
  in the recorded `Functoriality` module, reexported by this module.
- Proof imports: the recorded
  `Sheaf.AlgebraicGeometry.FundamentalGroup.FieldGaloisFibreIdentification`
  (`field_galois_fibre_identification`) and
  `Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence`
  (`exists_fiber_flc_equivalence` and its base-change companions).
  The remaining proof dependency `lem-dl-a1-profinite-restriction-full-faithful`
  has no Lean module recorded at the time of this delivery; no import can yet
  be added for it. Its proof role is retained in the docstring and DAG.
- Mathlib's `Functor.mapAut`, `Functor.whiskeringLeft`, `Iso.conjAut`, and
  `Mathlib.FieldTheory.Galois.Profinite` supply the standard constructions
  and topologies. The original statement-dependency notions are all from their existing
  modules or their recorded reexports.

Edge cases checked before finalizing the statement: empty finite-etale cover
(all compared point and section types are empty, trivial-action conditions
vacuous); the identity cover (all section and fibre sets are singletons);
separably closed K and trivial G (full faithfulness then forces trivial target);
imperfect fields in positive characteristic (Ω/Ks is purely inseparable,
not assumed trivial); characteristic zero; trivial and full subgroups H;
no finiteness or normality assumption on X; no essential-surjectivity assumption
on pullback. The empty scheme cannot carry the field point and is already
excluded by connectedness. Universes are explicit, `autoImplicit` is false,
and all schemes and fields use the standard common ambient universe with no
cardinality bound. No node fault or statement dispute was found.

Searches (2026-10-24):

- `msearch.py leanfinder`, query "Fully faithful pullback of finite etale covers
  along a field valued point induces a continuous surjection from its absolute
  Galois group onto the etale fundamental group and sections are fixed fibre
  points": eight hits, including `toAut_surjective_of_isPretransitive` and
  `AutGalois.π_surjective`. These require abstract transitivity or concern a
  Galois object, and do not state this field-point comparison and both section
  bijections.
- `msearch.py loogle`, query `Field.absoluteGaloisGroup, Continuous`: zero hits.
- `msearch.py grep`, query `galoisToAut|fundamentalGroupMap|FullyFaithful` in
  Mathlib `AlgebraicGeometry`: 25 reported hits, concerning fully faithful
  forgetful, Spec and module functors, not this assertion.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for `galoisToAut`,
  `pointOfAlgebra`, field Galois comparisons, and this item's ID: the field
  comparison dependency and GaloisAction/Restriction provide the reusable
  ingredients, but no declaration supplies the whole item. The exact proposed
  declaration name is absent also from `dag/lean_names_upstream.json`.

Validation: `scompile.py Q46 lem-dl-a1-field-point-full-faithful-galois-map`
compiled both the sandbox and named library module cleanly (10.3 s and 3.5 s).
Only the expected postponed theorem proof remains. The argument order of
Mathlib's `Functor.mapAut` was corrected during compilation; no mathematical
statement was changed.

## Second reading by Q46

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
