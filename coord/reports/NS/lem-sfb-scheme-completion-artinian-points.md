## Worker report

The module `Sheaf.AlgebraicGeometry.CompletedStalkArtinianPoints` states the whole
node as five theorems with `sorry`, with five concrete helper definitions belonging
to the canonical map and the displayed set in this same node. No definition is
chosen from an existence statement and no new mathematical notion is introduced.
The node's statement and dependency lists are unchanged.

Hypotheses and clauses, using namespace `AlgebraicGeometry.Scheme`:

- The base is `R : Type u` with `[CommRing R] [IsNoetherianRing R]`.
  The scheme is `Y : Scheme.{u}`, its structure map is `f : Y ⟶ Spec (.of R)`,
  and `[LocallyOfFiniteType f]` is exactly locally finite type. No quasi-compactness
  or separatedness is assumed.
- The point is `y : Y` and its residue field is the dependency's `Y.residueField y`.
  `stalkBaseRingMap f y` is explicitly GammaSpec inverse, pullback on global
  sections, then the germ at y. Composing it with `Y.residue y` gives the canonical
  R-module structure on the residue field. `hfinite : @Module.Finite ...` uses
  exactly this module structure, with no freely chosen action.
- The completed local ring is literally
  `AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
    (Y.presheaf.stalk y)`, using the recorded completion definition.
  Its canonical R-algebra structure is the composite of `stalkBaseRingMap` with
  the stalk algebra map into this completion. Commutation with this map is stated
  explicitly in `markedCompletedStalkMaps`; no arbitrary algebra structure on C
  is a parameter.
- `completedStalk_properties` asserts Noetherianity and locality of this C,
  `IsAdicComplete` for the kernel of `completedStalkResidueMap`, and surjectivity
  of that residue map together with `q x = 0 ↔ ¬ IsUnit x`. In a local ring the
  nonunits are exactly its unique maximal ideal; thus this kernel is precisely
  m_C, and the surjective map to the actual k specifies the canonical residue
  identification C/m_C = k. The residue map is concretely `AdicCompletion.evalOneₐ`.
- A test algebra is `A : Type u` with `[CommRing A] [IsLocalRing A]
  [IsArtinianRing A] [Algebra R A]`. Its specified residue marking is a ring map
  `q : A →+* Y.residueField y`, `hq` says surjective, and `hkernel` says its
  kernel is the maximal ideal (the nonunits). These data are exactly an
  identification of the residue field with k. `hbase` says this identification is
  over R, as required for an R-algebra with specified residue field k.
- `markedCompletedStalkMaps f y q` is precisely the left-hand set: `IsLocalHom v`,
  commutation with R, and `q.comp v = completedStalkResidueMap` (identity on k).
  `IsLocalHom` is Mathlib's unit-reflection property, equivalent for local rings
  to the inverse-image-of-maximal-ideal condition in the node.
- `completedStalk_markedArtinianPoints` asserts `Set.BijOn` of the actual
  composition map `completedStalkPointMap`. This means a bijection between the
  two specified sets, without inventing an arbitrary equivalence. The right-hand
  set imposes `a ≫ f = Spec.map (algebraMap R A)` and
  `Spec.map q ≫ a = Y.fromSpecResidueField y`, the over-R and marked-point
  conditions. `completedStalkToScheme` is Spec of the stalk-to-completion map
  followed by `Y.fromSpecStalk y`, exactly the canonical map of the node.
- The second conjunct asserts for every such v a positive n with
  `ker(completedStalkResidueMap)^n ≤ RingHom.ker v`, exactly killing m_C^n.
- `completedStalk_markedArtinianPoints_naturality` quantifies over both marked
  Artinian R-algebras and every `h : A →ₐ[R] A'` with `IsLocalHom` and the
  residue compatibility. It asserts closure of the left-hand set under h and
  the equality of its point with `Spec.map h ≫ point v`. There is no surjectivity
  restriction on h.
- `completedStalk_artinianQuotients`, for every n with `0 < n`, asserts the
  Artinian and local properties of C/m_C^n and its residue identification with k.
  The residue map is characterized by factoring the actual residue map of C.
  It also asserts the ring isomorphism to O_y/m_y^n with the formula on stalk
  elements, which uniquely specifies the coordinate isomorphism. The final
  equality identifies the canonical quotient point with the canonical
  infinitesimal-neighbourhood map after this isomorphism. Thus no arbitrary
  isomorphism or arbitrary infinitesimal map replaces the canonical ones.
- `completedStalk_artinianQuotients_transition` uses the actual
  `Ideal.Quotient.factor (Ideal.pow_le_pow_right hnr)` for all r ≥ n ≥ 1 and
  asserts the corresponding point equality, including r = n.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (all ideals FG).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `.Hom`,
  `AlgebraicGeometry.Spec`, `Spec.map` (scheme and affine-spectrum dependencies).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`.
- `Mathlib.Algebra.Field.Defs`: `Field`, inherited by `Y.residueField y`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `.residue`,
  `.Hom.residueFieldMap`, `.fromSpecResidueField`; the former is the actual
  `IsLocalRing.ResidueField` of the stalk, not an independently chosen field.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`,
  `IsAdicComplete`, `AdicCompletion.evalOneₐ`, completion algebra map.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- The size-convention node has no declaration: explicit `universe u` and all
  rings, schemes and test algebras in that universe implement its bound.

All available proof-dependency modules are imported, without `public`, including
`WeilConjectures.RingTheory.AdicCompletionNoetherian`, Mathlib's affine scheme,
stalk, Noetherian, finite-type algebra, localization, local-completion,
module-completeness, Hopkins-Levitzki and Krull-height modules. Public imports
supply the declarations occurring in the statement. Source read: local
`literature/stacks-project/artin.tex`, definition-versal and
lemma-versality-matches (Tag 0CXK), in particular its displayed equality of sets.

Edge cases checked before writing: empty Y supplies no y and makes no claim;
a zero base ring similarly supplies no scheme point over it; a test algebra
cannot be zero because it is local and has a residue-field marking. The field
case has zero maximal ideal and positive quotients equal to the field. The
quotient exponent 0 is deliberately excluded (its quotient would be the zero
ring), while n = 1 and the identity transition r = n are included. No continuity
assumption, residue-field section, finite-cardinality assumption, or surjective
transition-map assumption has been added. No characteristic is excluded. All
schemes and algebras range over the same arbitrary universe bound, including
the quotient test rings themselves.

Searches for an existing statement and helper constructions:

- `msearch.py ... leanfinder "The completed local ring of a scheme represents
  marked Artinian local algebra points"`: 8 hits, chiefly Artinian schemes and
  `SpecToEquivOfLocalRing`; that equivalence is about the uncompleted stalk and
  does not state this node.
- `msearch.py ... loogle "AdicCompletion, IsLocalRing"`: 12 hits including
  completion locality, completeness, local algebra map, and residue bijectivity.
  These supply ingredients; no full Artinian-point statement.
- `msearch.py ... grep "AdicCompletion.*[Hh]om|[Hh]om.*AdicCompletion|completion.*[Aa]rtinian"`:
  completion ring maps, `liftRingHom`, `evalOneₐ` and local-completion results;
  no combined scheme-point identification.
- `msearch.py ... leansearch "Local maps from the completed local ring of a
  scheme to an Artinian local ring represent scheme points with fixed residue
  field"`: 8 hits including `SpecToEquivOfLocalRing`, residue fields, residue
  maps and Artinian schemes. None states the completed version.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for completions, Artinian
  points, the node id and all ten proposed declaration names: other completion
  results and ordinary deformation-lifting statements, no exact statement or
  conflicting declaration. In particular the source's curve `AdelicLocal`
  confirms the same canonical base-to-stalk germ construction. The existing
  `evalOneₐ` and `fromSpecStalk` are used, not reconstructed.

No disputed statement or node correction. Definitions have full concrete data;
all five postponed theorems match clauses of this node and contain source and
step-by-step proof docstrings.

## Second reading by NS

Independent second reading by the maintainer reviewer, replacing the author's
self-check. It covers the delivery at 17837b8f. The node's statement is read
against Stacks artin.tex Tag 0CXK (lemma-versality-matches: Mor(R^,A) =
{Spec A -> U over S restricting to u0 on Spec k}) and Schemes Tag 01J6.

Node objects, hypotheses and clauses, with the Lean that renders each:

- R commutative Noetherian: `{R : Type u} [CommRing R] [IsNoetherianRing R]`
  (def-weil-pbc-noetherian-ring = IsNoetherianRing). OK.
- Y -> Spec R locally of finite type: `f : Y ⟶ Spec (.of R)`, `[LocallyOfFiniteType f]`
  (def-weil-finite-type-morphism record). There is no quasi-compactness or separatedness. OK.
- Size convention: R, Y, A all in universe u. `Spec (.of A) ⟶ Y` forces the test
  algebras into Y's universe, and C/m^n is in Type u as well. This is no silent restriction. OK.
- k = κ(y) finite as an R-module: `hfinite : @Module.Finite R (Y.residueField y)`. It uses
  the module structure of residue ∘ stalkBaseRingMap f y. stalkBaseRingMap is
  (ΓSpecIso R).inv ≫ f.appTop ≫ germ ⊤ y, the canonical structure map R -> O_{Y,y}. It is
  the same inline pattern as SurfacePointBlowupData and the nodal modules, and there is no
  def node for it. OK.
- C = completion of O_{Y,y} at m_y: literally `AdicCompletion (maximalIdeal stalk) stalk`
  (def-weil-pbc-adic-completion record = AdicCompletion). OK.
- C complete Noetherian local with residue field canonically k (completedStalk_properties):
  IsNoetherianRing, IsLocalRing, IsAdicComplete for ker(evalOneₐ), and evalOneₐ : C -> k
  surjective with kernel exactly the nonunits. So the kernel is m_C and C/m_C ≅ k
  through the canonical first coordinate. The R-algebra structure is the explicit composite
  R -> O_{Y,y} -> C, not a free instance. OK.
- C/m_C^n Artinian local with residue field k for every n ≥ 1
  (completedStalk_artinianQuotients, `0 < n`): IsArtinianRing and IsLocalRing. It also gives a
  residue map qn that factors evalOneₐ, which pins it uniquely, with kernel the nonunits. OK.
- Test algebra A: Artinian local R-algebra with specified residue field k. A has
  `[IsLocalRing A] [IsArtinianRing A] [Algebra R A]`. The marking is q : A -> k, surjective
  with kernel the nonunits, so it is exactly an identification A/m_A ≅ k. `hbase` makes the
  identification R-linear. hbase adds no stronger assumption: both sides of the bijection
  are empty without it. A marked v gives q∘algebraMap = residue∘base, and a marked a gives
  the same equation after composing with f. OK.
- Left set (markedCompletedStalkMaps): IsLocalHom v (for local rings, unit reflection
  equals "inverse image of m_A is m_C"), compatibility with R via the canonical composite,
  and q ∘ v = evalOneₐ ("inducing 1_k"). OK.
- Right set: `a ≫ f = Spec.map (algebraMap R A)` (over R) and
  `Spec.map q ≫ a = Y.fromSpecResidueField y` (a|Spec k = the canonical residue point). OK.
- The map is composition with the canonical Spec C -> Y: completedStalkPointMap v =
  Spec v ≫ (Spec(O_{Y,y} -> C) ≫ fromSpecStalk y). This is the canonical c ∘ Spec ι of proof
  step 4. The bijection is `Set.BijOn` of this actual map (MapsTo, InjOn, SurjOn). OK.
- Every v kills some m_C^n: `∃ n, 0 < n ∧ ker(evalOneₐ)^n ≤ ker v`. OK.
- Naturality in local R-maps h : A -> A' inducing 1_k, with no surjectivity:
  `h : A →ₐ[R] A'`, `IsLocalHom h`, `q' ∘ h = q`. The conclusion is that h∘v is marked and
  point(h∘v) = Spec h ≫ point(v). OK.
- C -> C/m_C^n correspond to the canonical infinitesimal neighbourhoods: there is
  e : C/m_C^n ≃+* O_{Y,y}/m_y^n pinned by e∘mk∘ι = mk. mk∘ι is surjective, so e is unique and
  not an arbitrary iso. It satisfies Spec e ≫ point(mk_n) = Spec(mk) ≫ fromSpecStalk y. OK.
- Compatibility with quotient transitions: point(mk_n) = Spec(factor_{r,n}) ≫ point(mk_r)
  for all r ≥ n ≥ 1, including r = n. Compatibility of the e's follows from their
  pinning. OK.

Edge cases: y with κ(y) = O_{Y,y} (a reduced isolated point): m = 0, C = k, and every
quotient is k. The DVR stalk with A = k[ε] works. Empty Y or the zero base supply no y.
A ≠ 0 because it is local. n = 0 is excluded exactly as the node's n ≥ 1. No
characteristic is excluded.

Records: the stmt_deps are unchanged and their lean records were checked: IsNoetherianRing,
Scheme, Spec, LocallyOfFiniteType, size convention (convention, no declaration),
Field/residueField, AdicCompletion/IsAdicComplete, Module.Finite. lean.statement is
verbatim the signature in the file (checked by substring). The five helper definitions
have real data, none chosen from an existence statement. All five theorems are `by sorry`
and carry source and step-by-step proof docstrings. The module docstring names Tag 0CXK /
01J6 and the blueprint id.

Searches: in the side-live lean/Sheaf and lean/WeilConjectures trees, none of the ten
declaration names occurs. The existing completed-stalk declarations
(NodalFiber.completedLocalRing of def-sfb-nodal-geometric-fibre-local-rings, and
AlgebraicGeometry.completedStalkMap of lem-trf-completed-stalk-isomorphism-etale) belong to
other nodes. They are not stmt_deps here, and they are the same Mathlib AdicCompletion. The
blueprint index has no def node for the completed local ring of a scheme or for the
base-to-stalk map. Mathlib has SpecToEquivOfLocalRing (uncompleted stalk) and the
AdicCompletion.LocalRing facts, but not this statement. No duplicate.

Mismatches found: none in the Lean or records. The only change is this section, which
replaces an author self-check (H11).
