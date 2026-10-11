## Worker report

The theorem module is `Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect`, declaration
`AlgebraicGeometry.affineMorphism_hom_out_of_perfect`. It states affine, stalkwise
Tor-independent base change for global derived Hom from a perfect object, with the
conclusion in the module derived category D(B), not in a sheaf derived category.
All theorem proofs are `sorry`. All definitions have actual bodies.

Hypothesis and clause correspondence:

- The rings R and R' are `{R B : CommRingCat.{uAH}}`, with no domain, nonzero-ring,
  Noetherian, finite-dimensional, flat, or finite-type restrictions.
- The original X is `{X : Scheme.{uAH}}`, with `[CompactSpace X]` and
  `[QuasiSeparatedSpace X]`. These are exactly quasi-compactness and quasi-separatedness.
- S and S' are literally `Spec R` and `Spec B`, in the types of `f` and `g`.
  Affine schemes are qcqs. The pullback X' is `pullback f g`; it is qcqs because f
  is qcqs (a morphism between qcqs schemes), and its base change is qcqs over S'.
  No extra independent compactness assumption on X' is needed.
- The structure morphisms are `(f : X ⟶ Spec R)` and `(g : Spec B ⟶ Spec R)`.
  The square is the chosen categorical pullback of `def-pc-fibre-product`, with
  `g_X = pullback.fst f g` and `f' = pullback.snd f g`; `pullback.condition` supplies
  its commutativity. Thus no cartesian-square hypothesis has been lost.
- Tor independence is `hTor : PullbackStalkTensor.IsTorIndependent f g`. I read this
  definition in full: it quantifies over EVERY pair x,t with f(x)=g(t), transports
  the second stalk algebra across that equality, and requires all positive Tor'
  objects to be zero. It does not just test points selected in X'.
- `M K : schemeDerivedCategory X` binds both complexes, with
  `hM : Scheme.IsPerfect X M` and `hK : schemeDerivedQCohProperty X K`.
  The latter requires each integer cohomology sheaf to be quasi-coherent.
  No boundedness assumption is imposed on K.
- The source is `(affineDerivedExtension g).obj
  ((schemeGlobalDerivedHomOver f).obj (op M,K))`: global RHom_X(M,K), restricted
  along R → Γ(X,O_X), then tensored-derived with B. The extension functor is
  characterized as a left adjoint of the exact derived restriction functor,
  which characterizes derived extension uniquely up to canonical isomorphism.
- The target is `(schemeGlobalDerivedHomOver (pullback.snd f g)).obj
  (op ((derivedPullback (pullback.fst f g)).obj M),
  (derivedPullback (pullback.fst f g)).obj K)`. It has the B-action induced by f',
  so the displayed arrow is in D(B).
- `IsIso (affineGlobalHomBaseChangeMap f g M K hM hK)` expresses invertibility
  of the canonical comparison in D(B). The body takes the extension/restriction
  adjoint of `globalHomPullbackComparison`. That definition chooses phi from
  `exists_globalHomPullbackComparison`, whose last equation fixes it to
  `(affineDerivedGlobalSections f).map (γ.app (op M,K)) ≫ c.hom.app (...)`.
  Gamma is constrained by the evaluation-mate equation of
  the normalized pullback and evaluation adjunctions now selected by the helper
  existence theorems (see repair X-248f2). The underived natural isomorphism s
  acts as identity on every section; the equation for c uses
  `rightDerivedFunctorCompUnit` and `rightDerivedFunctorUnit`, and is required
  at every homotopy object, in particular K-injective representatives.
  `affineGlobalSectionsDerivedIso` and `affineBaseChangedSectionsDerivedIso`
  are explicit unit-compatible isomorphisms for exact scalar restrictions.
  There is no unconstrained Nonempty Hom assertion and no affine model choices.
- The explicit derived-category instances, including the over-open instances needed
  by the recorded `Scheme.IsPerfect`, choose the category localizations. They are
  implementation structures, not extra geometric conditions. All modules and schemes
  use universe uAH and localization Hom universe wAH. There is no independently
  smaller test universe or bounded degree restriction.

Dependency declarations used (source files and complete signatures/docstrings read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme Hom.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, with its
  projections and commutativity. Mathlib has scheme pullbacks.
- `Sheaf.AlgebraicGeometry.PerfectComplex`: `Scheme.IsPerfect`, using its recorded
  `SheafOfModules.overFunctor` localization and `IsStrictlyPerfect` condition.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory` and
  `schemeDerivedQCohProperty`, using the shared sheaf-module category instance.
- `Sheaf.AlgebraicGeometry.DerivedPullback`: `derivedPullback`; its chosen functor
  is specified by the left-derived universal property and K-flat computations.
- `Sheaf.AlgebraicGeometry.GlobalDerivedHom`: `schemeGlobalDerivedHom` and
  `schemeDerivedGlobalSections`, using moduleRings global sections as coefficient ring.
- `Sheaf.AlgebraicGeometry.PullbackStalkTensorComparison`:
  `PullbackStalkTensor.IsTorIndependent`; its landed definition node was added to stmt_deps.
- The comparison uses the mate equation described in
  `derivedInternalHom_pullback_adjunction`, but does not select its unrestricted
  witnesses. It imports `SchemeDerivedBaseChangeMap` for the normalized
  `exists_schemeDerivedAdjunction` and `CanonicalDerivedTensorHom` for the
  evaluation-normalized `schemeDerivedTensorHomEquiv` and its representative predicate.
- `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition`:
  `RingedSpace.exists_derivedModuleDirectImageComposition`, whose right-derived
  unit equation gives the construction used to characterize c.
- `Sheaf.AlgebraicGeometry.DerivedSectionsPushforwardComparison`:
  `AlgebraicGeometry.derivedSectionsPushforwardComparison`. Its statement forgets
  scalars to abelian groups, so c is stated with the R-action retained, using the
  same composition mechanism; this is not a replacement of that dependency.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory`:
  `Functor.rightDerivedFunctorCompMapDerivedCategoryIso` and, through its Comp
  import, `Functor.rightDerivedFunctorCompUnit`. These supply the actual bodies
  of the two exact-restriction comparisons and the unit equation.
- Mathlib scalar restriction, its exact derived functor `mapDerivedCategory`,
  `Scheme.ΓSpecIso`, and the module extension/restriction adjunction are reused.

The previous carrier obstacle is resolved by passing BOTH R and S explicitly to
`ModuleCat.restrictScalars`, as the landed `GlobalHomAdjunction.lean` does. This
lets Lean elaborate `f.appTop.hom` against exactly the moduleRings section carrier.
No copied structure sheaf, alternative module category, or unproved type equality
is introduced.

Edge cases checked before writing: zero rings and their empty spectra; empty X;
zero M or zero K; identity g; arbitrary nonflat g satisfying Tor independence;
negative and unbounded cohomological degrees; no nonempty assumption on X or its
fibres. In the empty case the stalkwise condition is vacuous as it should be,
while all global derived Hom objects are zero. For identity base change the underived sections map is the identity; the
unit equation forces c to be its canonical derived identification, and the
evaluation-mate equation, with the corrected normalized adjunction choices,
makes gamma the corresponding pullback identification.
Thus phi is the canonical identification, rather than an arbitrary arrow.
The old zero-morphism construction cannot prove the replacement theorem: choosing
phi=0 still requires its equality with the specified composite. For a nonzero
identity-base-change object that composite is the identification, not zero. R and B can be any commutative rings
in the same arbitrary universe; no Noetherian or characteristic exclusions occur.

Searches made:

1. msearch LeanFinder: `global derived Hom of a perfect complex commutes with Tor
   independent affine base change`; 8 results about Tor, Ext, and exact functors,
   none states the scheme theorem.
2. msearch Loogle: `ModuleCat.restrictScalars, RingHom`; no theorem for this comparison.
   Loogle `ModuleCat.extendScalars`: 12 hits for the underived functor, its adjunction,
   units/counits and composition. These are used, not redefined.
3. msearch grep `RHom|TorIndependent` in AlgebraicGeometry and rg searches of
   WeilConjectures and lean/Sheaf for global RHom, scalar restriction, Tor independence,
   and Hom base change. No scheme global RHom base-change map or theorem exists.
   `PerfectRHomBaseChangeMap` is on a one-object ring site; it does not define
   global RHom on a general qcqs scheme. `GlobalHomAdjunction` has the correct scalar
   restriction syntax, but states a different adjunction theorem.
4. msearch LeanSearch: `derived extension of scalars global derived Hom base change`;
   unavailable (Internal Server Error), recorded as unavailable, with no mathematical
   no-match inference from that service.
5. Additional LeanFinder: `canonical affine base change map for global derived Hom
   from a perfect complex`; 8 Tor/Ext/derived-functor results, none a match.
6. DAG rg searches and `blueprint_refs.py search affine-global-hom`: no definition
   node for this comparison (0 blueprint matches). `blueprint_refs.py ancestor`
   confirms `lem-sc-finite-duality`. The exact item id has no occurrence in
   upstream WeilConjectures source.

Source fault: the node says Tag 0AVW but gives the label
`perfect-lemma-affine-morphism-and-hom-out-of-perfect`. The actual label maps to
Tag 0AA7, not 0AVW. I opened the current Stacks `perfect.tex` and its tags index;
the named lemma's case (1) is exactly the node's statement. The statement therefore
needs no correction. The theorem docstrings cite the named label (and the new node
records the correct tag). No STATEMENT-DISPUTED flag or dependency replacement is needed.
The unavailable local literature is read from the primary Stacks source online:
https://raw.githubusercontent.com/stacks/stacks-project/master/perfect.tex and
https://raw.githubusercontent.com/stacks/stacks-project/master/tags/tags .

Local validation: both delivery modules compile together with lcompile, with no
errors or warnings. Server validation is performed by the required deliver2 dry run.

## New nodes

`def-pc-affine-global-hom-base-change-map` supplies the affine global Hom comparison
in `Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap`. It reuses global RHom,
internal RHom, derived pullback and direct image. Its helpers give the base ring
map, underived and derived scalar restrictions, the exact-restriction comparison
isomorphisms, and derived extension as the left adjoint of restriction.
`exists_affineDerivedExtension` has a K-flat-resolution proof in words.
`exists_globalHomPullbackComparison` supplies adjunction and tensor-Hom witnesses,
gamma with its evaluation-mate equation, the underived sections identity s, c with
its derived-unit equation, and phi with its composite equation. All definitions
have explicit bodies. The map does not assume Tor independence, and its definition
does not assume invertibility. Its source is Stacks Tag 0AA7, with the sections
comparison and derived composition of Tags 08D5/0D5T. The existing searches above
found no declaration for this map; the new node records these searches individually.
Its title and statement now name gamma and the sections/pushforward comparison,
including the corresponding DAG dependencies. No model identifications remain.

## Repair of return 03f724ac9

1. Replaced the content-free Nonempty Hom theorem by a single existential package
   with the mate, sections, derived-unit, and phi-composite equations. Opened the
   body of phi and checked that it chooses the first witness phi of this package.
2. Renamed the new node and specified gamma and c in its statement; added both
   sections/pushforward and ringed-space composition node ids to stmt_deps.
3. Added source docstrings for derived extension and its adjunction and a complete
   K-flat/adjunction proof in words to the existence theorem.
4. Rewrote Worker report and New nodes, and repaired the theorem docstring, to
   describe the delivered construction. Removed the superseded second readings.

Repair searches: msearch Loogle `Functor.rightDerivedFunctorCompUnit` returned
unknown identifier (the declaration is upstream, not in indexed Mathlib); msearch
LeanFinder `canonical global derived Hom comparison induced by pullback and global
sections pushforward` returned eight underived pullback/adjunction results, no match.
rg of WeilConjectures and lean/Sheaf for `globalHomPullbackComparison` and
`affineGlobalSectionsDerivedIso` found no existing declaration; the exact item id
has no upstream occurrence. The replacement reuses the upstream composition unit.
Source rechecked: [Stacks 0AA7](https://stacks.math.columbia.edu/tag/0AA7) defines
this map as the adjoint of the pullback-induced global Hom map; [Stacks 0D5T]
(https://stacks.math.columbia.edu/tag/0D5T) supplies derived composition.


## Earlier second reading (a previous round; superseded)

Independent second reader, 2026-10-12. I opened both node copies, both delivery
modules, every recorded statement-dependency signature and the definition bodies
listed below. I also read the Stacks perfect.tex lemma
`lemma-affine-morphism-and-hom-out-of-perfect` and its proof, fetched from the
primary Stacks source into the item's scratchpad. Its case (1) agrees with the
item. The surrounding section imposes no additional ring, characteristic,
Noetherian or boundedness assumptions. The named label is Tag 0AA7; the base node's
0AVW is a citation typo, not a different intended statement. I have not changed
any field of the base node other than the permitted delivery fields.

Object/hypothesis/conclusion list and individual correspondence (H3):

1. Arbitrary commutative base rings R and R': `{R B : CommRingCat.{uAH}}`.
   Verdict: matches; B renders R', without a field or nonzero-ring restriction.
2. Affine S and S': the codomain of f is `Spec R`, and g has type
   `Spec B ⟶ Spec R`. Verdict: matches the entire affine-base case, not a
   restriction of X to an affine scheme.
3. Qcqs X: `{X : Scheme.{uAH}} [CompactSpace X] [QuasiSeparatedSpace X]`.
   Verdict: matches. The affine bases are qcqs automatically. A morphism from a
   qcqs scheme to an affine scheme is qcqs, so its base change has qcqs source
   over the qcqs affine Spec B. The absent independent qcqs binders on X' thus
   omit no geometric hypothesis.
4. Cartesian square, both structure maps and both projections: `(f : X ⟶ Spec R)`
   and `(g : Spec B ⟶ Spec R)`, with X'=`pullback f g`,
   g_X=`pullback.fst f g`, f'=`pullback.snd f g` throughout the map.
   Verdict: matches via the chosen categorical pullback; every other cartesian
   square is isomorphic to this one. Commutativity is built in, not an extra
   conclusion or a hollow hypothesis.
5. Tor independence for every pair of points over one base point and every
   positive degree: `hTor : PullbackStalkTensor.IsTorIndependent f g`.
   I read its body: it quantifies over all x,t and all equalities f(x)=g(t),
   uses the actual stalk maps and transports the second scalar action along
   that equality, and imposes `IsZero` on `Tor' ... i` for every natural i>0.
   Verdict: exactly the node's condition, not just selected pullback points,
   and neither flatness nor finite Tor dimension is substituted.
6. Objects M,K in D(O_X): `(M K : schemeDerivedCategory X)`.
   Verdict: the shared derived category of module sheaves is used.
7. Perfectness of M: `hM : Scheme.IsPerfect X M`. I read `IsPerfect` and
   `IsStrictlyPerfect`: every point has an open neighbourhood on which M is
   isomorphic to a bounded complex of summands of finite free module sheaves.
   Verdict: the recorded geometric notion, not global strict perfection.
8. Quasi-coherent cohomology of K: `hK : schemeDerivedQCohProperty X K`.
   Its body requires quasi-coherence in every integer degree. Verdict: matches
   D_QCoh(X), without a lower or upper bound.
9. Global RHom with its R-action: `schemeGlobalDerivedHomOver f`, whose body
   composes the recorded internal Hom and `schemeDerivedGlobalSections X`
   with exact scalar restriction along R → Γ(X,O_X). I read the recorded
   `schemeGlobalDerivedHom` body: it is the same first two functors.
   Verdict: the node's global complex, not internal Hom alone or abelian Hom.
10. Derived tensor over R with B: `affineDerivedExtension g`, selected from
    `exists_affineDerivedExtension`, with `affineDerivedExtensionAdjunction`.
    Verdict: the left adjoint to exact restriction along `affineBaseRingMap g`
    realizes derived scalar extension, uniquely up to adjunction-compatible
    isomorphism; its source and target are module derived categories.
11. Target with both objects pulled back: `schemeGlobalDerivedHomOver
    (pullback.snd f g)` evaluated at
    `(op ((derivedPullback (pullback.fst f g)).obj M),
    (derivedPullback (pullback.fst f g)).obj K)`.
    Verdict: both pullbacks and the B-action agree with the node.
12. Canonical arrow and isomorphism in D(B): `IsIso
    (affineGlobalHomBaseChangeMap f g M K hM hK)`.
    I traced its body to the inverse `homEquiv` of extension/restriction,
    applied to `globalHomPullbackComparison`. The selected phi is constrained
    by its equation with RΓ of gamma followed by c. Gamma obeys the same
    evaluation-mate equation as the third conjunct of the recorded
    `derivedInternalHom_pullback_adjunction`; the orientations of t.inv,
    evaluation, bT.homEquiv and a.homEquiv.symm agree. The underived s acts as
    identity on all sections. The equation for c holds on every homotopy
    object and relates the composite derived unit to the unit after s,
    using the two exact-restriction comparison isomorphisms. Verdict: the
    specified comparison, not an unconstrained arrow or an assertion that
    some arrow exists. No assumption of its invertibility enters the definition.

The `HasDerivedCategory` binders provide shared localization structures, including
on all opens used by the recorded perfectness predicate. They introduce no
finiteness or boundedness condition. All rings and schemes share an arbitrary
universe uAH; the localization Hom universe wAH is explicit. Objects from different
small universes can be placed in a common universe. There is no independently
smaller universe of test objects and no free universe or variable left implicit.

Dependency reading: I opened DerivedCategory, PerfectComplex, GlobalDerivedHom,
DerivedPullback and PullbackStalkTensorComparison and checked their bodies, not
just their names. The pullback is Mathlib's categorical scheme fibre product.
I read DerivedInternalHomPullbackAdjunction's full existential package, including
its evaluation equation; RingedSpaceDerivedDirectImageComposition's unit-compatible
comparison; and DerivedSectionsPushforwardComparison's abelian-group-valued
signature. The latter alone would lose the R-action: the delivered c correctly
retains scalars and imposes the composition-unit equation instead. The upstream
MapDerivedCategory and Comp declarations give the two actual exact-restriction
comparisons and `rightDerivedFunctorCompUnit`. The scalar ring carriers are the
recorded `moduleRings`, not a private replacement. No unusable dependency or
missing definition remains, and no dependency module is being delivered.

New-node reading (H12): `def-pc-affine-global-hom-base-change-map` describes exactly
the gamma/c/phi construction above and the extension/restriction mate from Stacks
0AA7, with derived composition as in 0D5T. Its dependencies cover the rings' scheme
objects, the fibre product, perfectness, derived categories, global RHom, pullback,
adjunction, internal-Hom mate and sections/composition comparisons. It is absent
from the base DAG and library. Its kind/status, chapter/unit, created record,
blueprint ancestor/via, empty proof fields, null mathlib_match, lean_audit and Lean
record meet the new-definition field rule. It is cited by the item. Its searches
include an explicitly unavailable LeanSearch service, with no no-match inference
from that failure. All helper definitions have bodies; only the two named
existence theorems postpone proofs. Their docstrings explain the K-flat descent
and the four-step construction, respectively. The item theorem's docstring carries
all four proof steps of the node. Every theorem in this delivery remains `sorry`.

Independent searches (H4), performed with different queries from the first reader:

- msearch LeanFinder: `derived global Hom perfect complex Tor independent change of
  affine base`: 8 hits on affine stability and scheme flatness, no global RHom
  base-change theorem or map.
- msearch Loogle: `ModuleCat.extendRestrictScalarsAdj`: 6 hits on the existing
  underived adjunction and its formulas; these supply scalar-change infrastructure,
  not the unbounded scheme global RHom statement.
- msearch grep: `derived.*Hom.*base|TorIndependent`: 0 hits in its indexed search.
- Direct rg of Mathlib, WeilConjectures, project Sheaf modules and DAG with
  `global.*[Hh]om.*[Bb]ase`, `[Hh]om.*[Bb]ase[Cc]hange`, `RHom.*[Bb]ase`,
  `affineDerivedExtension`, `schemeGlobalDerivedHomOver` and `affine-global-hom`:
  no existing general scheme comparison. I opened the project algebraic
  BaseChangeRHomPerfect statement: its ring-site objects and explicit model data
  differ from this qcqs scheme theorem. It does not replace this delivery.

Edge cases: empty X, zero rings/empty affine bases, zero M or K, identity g,
nonflat g satisfying Tor independence, degree zero, negative degrees and unbounded
K are admitted. Empty X makes perfectness and stalkwise Tor independence vacuous,
as required, and global sections are zero. There is no index set here; the local
perfectness quantifier covers an empty scheme without a nonempty covering
assumption. No characteristic, nontriviality, Noetherian or finite-type binder
excludes a source case. Identity base change tests the specified comparisons;
phi cannot be replaced by an arbitrary zero arrow because of its composite
equation.

Mismatches repaired: two helper docstrings (`affineBaseRingMap` and
`schemeGlobalDerivedHomOver`) lacked explicit source places; both now cite Stacks
0AA7. The comparison docstring counted three equations although it has four
(gamma, s, c and phi); the count is corrected. I normalized a broken introductory
line in the item docstring. No mathematical signature or definition body was
changed; the node Lean signatures remain verbatim equal to their declarations.
Local compile of both modules together passed cleanly (15.4 seconds, exit 0).
The shared parser located both signatures, and their verbatim source slices agree
with the node Lean records. The deliver2 dry run also passed server compilation
and preflight: OK, nothing pushed.


## Earlier repair X-2462d: withdrawn normalization claims

The earlier claim that `derivedInternalHom_pullback_adjunction` carries the underived
unit and evaluation normalization equations was incorrect. Its unrestricted witnesses
can be sign-twisted as X-248f2 describes. Also, the delivered `t` constraint was
`IsCanonicalPullbackTensorComparison`, a K-flat characterization, not equality to a
`canonicalPullbackTensorComparison` selection. Those inaccurate claims are withdrawn.
The second-reading text below describes the preceding delivery; the present repair
still awaits the dispatcher's independent second reader.

## Earlier second reading (a previous round; superseded)

I reread the item node, the new definition node, the recorded declarations of every
statement dependency, and the Stacks source at `perfect.tex`,
`lemma-affine-morphism-and-hom-out-of-perfect`, case (1). The source's actual label is
Tag 0AA7; the node's Tag 0AVW is a citation typo. The source assumes a cartesian square
of qcqs schemes, `S = Spec(R)`, `S' = Spec(R')`, Tor independence, and either (1)
perfect `M` with `K` quasi-coherent or (2) the separate pseudo-coherent/finite-Tor case.
This item is case (1), exactly.

Object and hypothesis matching:

1. `R B : CommRingCat.{uAH}` renders arbitrary commutative `R,R'`; no field,
   nonzero, Noetherian, finite-type, characteristic, or finite-dimensional hypothesis.
2. `f : X ⟶ Spec R` and `g : Spec B ⟶ Spec R` render the affine bases and both
   structure maps. `pullback f g`, `pullback.fst f g`, and `pullback.snd f g` render
   `X'`, `g_X`, and `f'`; the categorical pullback supplies the cartesian square.
3. `[CompactSpace X] [QuasiSeparatedSpace X]` render qcqs `X`; affine bases and their
   pullback have the required qcqs properties. No extra condition is assumed on `X'`.
4. `hTor : PullbackStalkTensor.IsTorIndependent f g` quantifies all `x,t`, every
   equality of their images, and every positive Tor degree using the actual stalk maps.
5. `M K : schemeDerivedCategory X`, `hM : Scheme.IsPerfect X M`, and
   `hK : schemeDerivedQCohProperty X K` render `M,K ∈ D(O_X)`, perfectness, and
   quasi-coherent cohomology, with no boundedness restriction on `K`.
6. The conclusion is `IsIso (affineGlobalHomBaseChangeMap f g M K hM hK)`. Its source
   is derived scalar extension of global RHom along `R → B`; its target is global RHom
   after both derived pullbacks, with the `B` action retained by restriction of scalars.
   Thus it is precisely the canonical map in `D(B)`, and all quantifiers and clauses
   agree with the source.
7. The two universal derived-category instance binders use the same universe `uAH`
   and localization universe `wAH`; they do not exclude empty schemes, zero rings,
   zero complexes, identity base change, or arbitrary characteristic.

The definition node's map has actual bodies for scalar restriction, derived extension,
and the comparison. I checked that its `gamma`, `s`, `c`, and `phi` witnesses are tied by
the mate, section-identity, right-derived-unit, and final composite equations, rather
than an unconstrained existential. I repaired its dependency accounting to cite the
landed normalized derived pullback adjunction (`def-pc-derived-base-change-map`) and
the landed K-flat characterization of the pullback tensor comparison
(`def-pc-derived-pullback-tensor-comparison`). I removed the unused private tensor
comparison helper and used the shared `schemeGlobalDerivedHom` carrier followed by the
recorded exact scalar restriction. No hollow definition was introduced; the only proofs
remain named `sorry` theorems. The item theorem itself remains unchanged and is still
proved by `sorry`.

Edge cases checked: empty `X` and empty spectra, zero `R`, `B`, `M`, or `K`, identity
`g`, non-flat but Tor-independent `g`, negative and unbounded cohomological degrees,
and arbitrary universes. The Tor condition is vacuous on an empty point set, as in the
source, while the derived Hom comparison remains the canonical zero/identity map.

Searches: LeanFinder and Loogle found only generic Tor, Ext, and change-of-rings APIs;
LeanSearch was unavailable and is recorded as such. Grep over Mathlib, WeilConjectures,
lean/Sheaf, and the DAG found no existing scheme global RHom affine base-change map.
The project's `PerfectRHomBaseChangeMap` is an algebraic one-object construction and is
not this theorem. The source and tag index were read directly; no existing declaration
matches either delivered node.

Compilation: `lcompile.py` compiled both delivery modules together with no errors or
warnings. The only changes made in this second reading are the dependency additions and
the shared-carrier/normalization repair described above.

## Repair of return reviewer X-248f2 (H3/H12)

`canonicalPullbackAdjunction` now uses exactly the prescribed selection from
`exists_schemeDerivedAdjunction`, with additivity, the left-derived counit, and its
universal property all selected from `exists_derivedPullbackComposition`. It no
longer selects any witness from `derivedInternalHom_pullback_adjunction`.
That upstream package does not carry the claimed underived normalization equations.

The named helper theorem `exists_canonicalTensorHomAdjunction` now requires
`IsCanonicalDerivedTensorHom S (fun A K L => ((b K).homEquiv A L).symm)` and
`(b K).counit.app L = schemeDerivedTensorHomEquiv S (RHom(K,L)) K L (𝟙 _)`.
The first condition spells out the localized Hom-complex evaluation on K-flat
representatives into the fixed K-injective resolution, with actual product
projections, underived sheaf tensor-Hom uncurrying, total-tensor summand inclusions,
localization tensor map, localization factorization and inverse resolution map.
The second condition specializes that normalized uncurrying to evaluation itself.
Thus the theorem requires evaluation normalization, rather than mere existence
of an adjunction or equality to another unrestricted witness. The canonical
adjunction selects its family from this named theorem. Pointwise bS/bT equalities
are retained, now using `canonicalTensorHomAdjunction X` and the corresponding
family on `pullback f g`.

The new theorem is recorded in the helper node's `lean.declarations`. Its existing
DAG owner is `def-pc-affine-global-hom-base-change-map`; it supplies the proof
needed to define that node's canonical comparison, not a second notion. The helper
node now cites the landed `def-pc-canonical-derived-tensor-hom-bijection`, module
`Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom`, using its recorded
`schemeDerivedTensorHomEquiv` and `IsCanonicalDerivedTensorHom`.
No dependency module or new definition is needed. Its proof docstring gives the
natural-bijection adjunction construction and the representative evaluation argument.
The prescribed pullback selection uses `Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap`
and its existing dependency `DerivedPullbackComposition`.

The `IsCanonicalPullbackTensorComparison` K-flat constraint on t, and the gamma,
section identity s, right-derived-unit c, and final phi composite equations, are
retained. No claim of equality to a chosen tensor isomorphism is made.

Identity base-change check (mathematical, stage 2 leaves proofs postponed): identify
`X ×_Spec(R) Spec(R)` with X by the canonical pullback projection. On K-flat
representatives, termwise identity pullback, the shared left-derived counit and
localization maps identify t with the ordinary tensor comparison, with positive
pure-tensor signs. The normalized underived unit identifies a with the identity
adjunction. Both b families now give the same localized evaluation. Consequently
the mate equation transposes evaluation to the identity of RHom(M,K). The section
identity makes s the ordinary identification, and the right-derived-unit equation
makes c the ordinary derived identification. Thus phi is the identity in these
coordinates. Transposing under the chosen extension/restriction adjunction gives
the canonical unit-compatible extension identification; the extension functor need
not literally equal the identity functor. Negating a.homEquiv and a.counit now
violates the prescribed underived normalization wherever 2 is nonzero; negating
b's counit violates the fixed evaluation equation. For example on Spec(ℤ) with
M=K=O[0], evaluation at 1 is +1 and the proposed negative comparison is -1.
In characteristic 2 those two maps agree, so there is no distinct negative map.
Zero objects and empty schemes likewise do not create a sign ambiguity.
This is a semantic identity check, not a new Lean proof of an identity theorem.

Repair searches: `msearch.py leanfinder "derived tensor Hom adjunction counit equal
localized Hom complex evaluation"` returned eight generic Tor/adjunction hits,
none with this scheme representative normalization. Grep in Mathlib, upstream,
and landed Sheaf modules found no existing `exists_canonicalTensorHomAdjunction`.
The broader evaluation search found the landed `CanonicalDerivedTensorHom` module;
its full signatures, representative predicate and node were read and reused.

Validation of this repair: both delivery modules compiled together locally with
no errors or warnings (25.8 seconds, exit 0). The helper's public map signature
is unchanged and still matches its node record. All theorem proofs remain `sorry`;
there are no proof additions or hollow definition bodies.

## Second reading by C1

I independently opened the item node, its Lean module, the Stacks source at
`perfect.tex`, `lemma-affine-morphism-and-hom-out-of-perfect` (case (1)), and the
recorded dependency declarations. The source assumes a cartesian square of
quasi-compact and quasi-separated schemes, affine `S=Spec(R)` and
`S'=Spec(R')`, Tor independence of `f` and `g`, and either the perfect/QCoh case
or a separate pseudo-coherent case. This item is exactly the first case. The node
labels the source as Tag 0AVW, while the current Stacks tag index identifies the
named lemma as Tag 0AA7; this is a citation-label typo and does not alter the
statement.

Object and hypothesis correspondence, in node order:

1. `R` and `R'` are rendered by `{R B : CommRingCat.{uAH}}`; no field,
   nonzero, Noetherian, finite-type, characteristic, or dimension restriction is
   added. `B` is the node's `R'`.
2. `f : X ⟶ Spec R` and `g : Spec B ⟶ Spec R` render both affine bases and
   structure maps. `pullback f g`, with `pullback.fst f g` and
   `pullback.snd f g`, renders `X'`, `g_X`, and `f'`; the categorical pullback
   supplies the cartesian square and its commutativity.
3. `[CompactSpace X] [QuasiSeparatedSpace X]` renders qcqs `X`. Since both
   bases are affine, the displayed morphisms and their pullback have the qcqs
   properties required by the source; no independent condition on `X'` is
   omitted.
4. `hTor : PullbackStalkTensor.IsTorIndependent f g` is the recorded
   stalkwise condition: it quantifies every pair of points over a common point
   and every positive Tor degree using the actual stalk maps. It is neither
   replaced by flatness nor restricted to selected pullback points.
5. `(M K : schemeDerivedCategory X)` renders two objects of `D(O_X)`, while
   `hM : Scheme.IsPerfect X M` is the recorded local perfectness predicate and
   `hK : schemeDerivedQCohProperty X K` requires quasi-coherent cohomology in
   every degree. No boundedness condition on `K` is present.
6. The conclusion is `IsIso (affineGlobalHomBaseChangeMap f g M K hM hK)`.
   The definition's source is derived extension of the global derived Hom along
   the affine ring map and its target is global derived Hom after both derived
   pullbacks, with the `B`-module structure retained. Thus the comparison is in
   `D(B)`, as the node says, and both quantifier order and clauses agree.
7. The explicit `HasDerivedCategory` binders (for all schemes, module rings,
   and opens of `X`) are implementation structures needed by the recorded
   derived-category declarations; they impose no geometric, finiteness,
   boundedness, nonemptiness, or universe restriction beyond the node.

I opened the dependency modules for the scheme, fibre product, perfect complex,
derived category, derived pullback, global derived Hom, affine global Hom map, and
stalk tensor comparison. Their declarations are the notions named by the node;
no private replacement or second definition is used. The affine comparison map's
body is a specified adjoint of the pullback-induced global Hom comparison, with
the normalized internal-Hom mate, section identity, derived-unit compatibility,
and final composite equation. It is therefore a canonical comparison rather than
an arbitrary morphism. The item theorem has a `sorry` proof only, and every
helper definition has data (the postponed arguments are named existence theorems),
so no hollow definition or proved statement was introduced.

Edge cases checked: empty schemes and empty spectra, zero rings, zero `M` or `K`,
identity base change, non-flat Tor-independent base change, arbitrary
characteristic, degree zero and negative/unbounded cohomological degrees, and the
shared arbitrary universe. The Tor condition is vacuous on an empty point set,
and no nonempty or Noetherian hypothesis is silently introduced.

Independent searches used `rg` over Mathlib, the upstream `WeilConjectures`
source, landed `lean/Sheaf`, and DAG nodes for global RHom/base-change names;
only the delivered affine comparison was found. LeanFinder/Loogle searches for
an affine perfect-complex global RHom base-change map returned only generic
Tor/Ext/scalar-change APIs. The project's ring-site perfect RHom map is a
specialized algebraic construction and does not state this qcqs scheme theorem.
No existing declaration matches the item.

No mismatch in the mathematical signature was found, so no Lean or node
statement was changed. The only source discrepancy is the pre-existing Tag 0AVW
label typo noted above; the source's named lemma and case (1) agree with the
node. Local compilation of the item and its affine comparison dependency together
completed without errors or warnings.
