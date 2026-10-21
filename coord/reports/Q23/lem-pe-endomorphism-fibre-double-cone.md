## Worker report

The delivery states `CochainComplex.EndomorphismFibreDoubleCone.exists_interchange`
in `Sheaf.Algebra.Homology.EndomorphismFibreDoubleCone`. Its only postponed proof
is this theorem, with the six steps of the node's proof in its docstring. The
six auxiliary declarations have real data: two transparent specializations of
Mathlib maps, the specified signed shift sigmaOne, and three predicates spelling
out projection identities. They belong to this node's prescribed construction; no new mathematical notion or
DAG node is needed. No live source was modified, and no Git command or local
Lean compilation was run directly.

The node's mathematical statement, proof and proof dependencies are unchanged.
Its statement dependencies remain exactly the two original definition nodes.
The returned head 30a72bc98408 unnecessarily added theorem node
`lem-weil-signed-mapping-cocone-shift` merely to use definitions from its module.
This repairs H2 by the reviewer's explicit alternative: use Mathlib's
`mappingCone.map` and its -1 shift directly, define the required sigma_1 in
this item's own module as `sigmaOne`, remove the signed-shift theorem import,
and drop the added statement dependency. The conclusion of that theorem,
`coconeCommShift`, is neither assumed nor used. No new node or dependency
module is needed for these helpers of this item's prescribed construction.
The suggested CompactObject example is now a withdrawn module; its node was also read.

### Hypothesis and clause correspondence

Lean composition `a ≫ b` means first a, then b. Thus the node's fs=tf is
`s ≫ f = f ≫ t`, and its fJ=J'g is `J ≫ f = g ≫ J'`.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Arbitrary abelian category | `{D : Type u} [Category.{v} D] [Abelian D]`, with independent explicitly declared universes u and v |
| Integer cochain complexes and chain maps | `CochainComplex D ℤ` and its categorical morphisms |
| Cone differential (db+fa,-da), boundary -p | The existing `mappingCone` and `(mappingCone.triangle f).mor₃`; the latter is defined from `-mappingCone.fst f` |
| Endomorphisms s,t and commuting chain map f | Universal binders `(s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t)` |
| K(A,s)=Cone(s)[-1] with reordered coordinates (v,u) | `mappingCocone s`, defined in Mathlib as `(mappingCone s)⟦(-1 : ℤ)⟧`; projections `mappingCocone.fst` and `mappingCocone.snd` give v and u, with differential (dv,-du-sv) |
| K(f)=diag(f,f) | `fibreMap s t f h`, transparently `(mappingCone.map s t f f h)⟦(-1 : ℤ)⟧'` |
| c=diag(t,s) on C=Cone(f), a chain endomorphism | `coneEnd s t f h`, transparently `mappingCone.map f f s t h.symm`; this is an actual chain map |
| Chain isomorphism Phi | The existential family `e` has type `mappingCocone (coneEnd s t f h) ≅ mappingCone (fibreMap s t f h)` |
| Phi(b,a,b',a')=(b,b',a,-a') in the specified orders | `Formula`: four degreewise equations for target projections b,b',a,h, with right sides b,b',a,-a' of the source |
| Inverse (b,b',a,h)=(b,a,b',-h) | `InverseFormula`: the four projections of `e.inv` are b,a,b',-h; the type `Iso` also supplies both inverse identities |
| Naturality for strict squares intertwining s,t | Second conjunct: f,f',s,t,s',t',alpha,beta are universally quantified with `hα`, `hβ`, `hsq`; the displayed equality is K(Cone(alpha,beta)) followed by Phi_f' = Phi_f followed by Cone(K(alpha),K(beta)) |
| The indicated induced maps are defined | `hc` and `hk` are existentially asserted intertwining equations in the conclusion, then used to construct the existing cocone/cone maps; they are not additional assumptions |
| Phi K(i)=i_K(f) | Third conjunct, first equation: the `fibreMap` of `mappingCone.inr f`, followed by `e.hom`, equals `mappingCone.inr (fibreMap s t f h)` |
| sigma_1 K(-p)=(-p_K(f)) Phi | Third conjunct, second equation: the `fibreMap` of `(mappingCone.triangle f).mor₃`, then `(sigmaOne s).hom`, equals `e.hom` then the target triangle's mor₃ |
| sigma_1(v,u)=(v,-u) | `sigmaOne s`, constructed from the inverse `mappingCone.shiftIso s 1`, its -1 shift, the shift commutator and scalar `1.negOnePow`; these fix coefficients 1 on v and -1 on u, including canonical degree transports |
| g,M,M',J,J' arbitrary with sJ=tJ'=0 and fJ=J'g | Last conjunct: universal complexes and maps, the two zero-composite premises and named binder `hJ : J ≫ f = g ≫ J'` |
| J_C diagonal cone map (J'm',Jm) | Mathlib's `mappingCone.map g f J J' hJ.symm` |
| eta_J, eta_J', eta_JC are chain maps with coordinates (J,0) | Existential morphisms eta,eta',etaC in the cochain category, satisfying the three `Augmentation` predicates; each predicate fixes the first projection to the specified J and every second projection to zero |
| The strict square K(f) eta_J = eta_J' g | Existential proof `hs : g ≫ η' = η ≫ fibreMap s t f h`, in the conclusion |
| Phi eta_JC = Cone(eta_J,eta_J') | Final equation `ηC ≫ (e s t f h).hom = mappingCone.map g (fibreMap s t f h) η η' hs` |
| No countable-product, boundedness, surjectivity assumptions | None of these classes or premises occurs anywhere in the module |

The augmentations are not unconstrained comparison maps: their two projections
uniquely specify them by the finite-biproduct decomposition. Likewise `Formula`
uniquely specifies Phi and `InverseFormula` specifies its inverse. An existential
family records the simultaneous natural isomorphisms without introducing an
object chosen from an undetermined existence theorem. All definitions contain
real terms; the theorem's single `sorry` is the only postponed proof.

### Dependencies and source declarations read

- `def-sp-abelian`: `CategoryTheory.Abelian` in
  `Mathlib.CategoryTheory.Abelian.Basic`, the class with preadditivity, normal
  monos/epis, finite products, kernels and cokernels. No special model of an
  abelian category is imposed.
- `def-weil-abstract-derived-category`: its Mathlib record identifies the
  cochain category, shifts and cones used here, as well as `DerivedCategory`
  and `DerivedCategory.Q` in `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
  The latter signatures and docstrings were read; this item only concerns the
  complex-level constructions, so no localization or `HasDerivedCategory`
  hypothesis is introduced. The actual definitions `mappingCone`, its
  projections and `mappingCone.triangle` were read in MappingCone.lean and
  Pretriangulated.lean, and `mappingCocone`, its projections and lifts were
  read in MappingCocone.lean.
- The cone and fibre maps use `CochainComplex.mappingCone.map` from
  `Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated` and the ordinary
  shift functor on morphisms. Its complete signature is `map φ₁ φ₂ a b
  (comm : φ₁ ≫ b = a ≫ φ₂)`. The triangle and its negative boundary are also
  from Pretriangulated. `sigmaOne` uses that module's `mappingCone.shiftIso`
  and `CategoryTheory.shiftFunctorComm`, without importing any project theorem.

The blueprint source was read at
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-lem-pe-derived-nakayama/sk-lem-pe-derived-nakayama-first-reduction.proof.md`,
Cones paragraph. It asserts functorial cone commutation and compatibility of
canonical triangle maps. The expanded node supplies the precise finite
coordinate statement. Stacks sources `derived.tex`, definition-cone and
its distinguished-triangle paragraph (Tags 014E, 014Q), and `homology.tex`,
definition-shift-cochain (Tag 011G), were read: they confirm the negative
boundary and the absence of a sign on shifted morphisms.

### Edge cases checked

These are mathematical projection checks, not additional proved Lean results.
For zero complexes the projection conditions and isomorphisms reduce to the
unique zero-object maps. For f=0 the differentials separate and Phi still
permutes the middle coordinates and negates the last. For s=t=0, the fibre
differential is (dv,-du); the mixed f terms in the double cones still match
with the specified minus sign. For identity endomorphisms no acyclicity is
assumed; the same chain-level calculation applies. A nonzero differential
commuting with s is handled by the displayed source and target differentials,
which agree after the signed permutation without assuming d=0. In
characteristic two the signs coincide but both inverse and boundary equations
remain valid. For J=J'=0 or g=0, the uniquely fixed zero-coordinate
augmentations and cone equation still specialize correctly. All degree
expressions use arbitrary integers; there is no truncated range or size
restriction on objects or morphisms.

### Searches

All wrapper searches used group Q23 and item
lem-pe-endomorphism-fibre-double-cone on 2026-10-21.

- `msearch.py leanfinder`: "Mapping fibres of commuting chain endomorphisms
  commute with mapping cones by signed permutation of four summands naturally
  with boundaries and augmentations". Eight hits, including
  `mappingCone.map_comp`, `mappingCone.map_δ`, `map_inr`, the additive-functor
  component isomorphisms and composable-cone homotopy equivalences. None
  states this strict endomorphism-fibre interchange with its augmentations.
- `msearch.py loogle`: `"mappingCone", "mapTriangle"`. Two hits,
  `mappingCone.mapTrianglehIso` and `mappingCone.mapTriangleIso`; these concern
  an additive functor applied degreewise, not a fibre mixing adjacent degrees.
- `msearch.py leansearch`: "The mapping fibre of an endomorphism on a mapping
  cone is isomorphic to the cone of its fibre map naturally with inclusion
  boundary and augmentation". Eight hits: the preceding additive-functor
  results and the ordinary mapping cone. No exact match.
- `msearch.py grep`, Mathlib Algebra/Homology:
  `mappingCocone|mapTriangleIso|mappingConeCompHomotopyEquiv`. Twenty-three
  hits in Pretriangulated, MappingCocone, Triangulated, Factorizations/CM5a and
  DerivedCategory/Basic. The relevant definitions/signatures were inspected.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `mappingCocone|endomorphismFibre|endomorphismFiber|doubleCone`, then
  `endomorphism.fibre|endomorphismFibre|EndomorphismFibre|signedFibre|signed.*[Cc]one`:
  existing Roos/shift constructions and SignedFibreCone were found. The latter
  has additive functors to AddCommGrpCat as data and a different domain; it
  does not state the present arbitrary-category/endormorphism assertion.
  The earlier packet used SignedMappingCoconeShift; this repair removes that import.
- `grep -rn` for the exact item id in `lean/WeilConjectures`: no hits.
  `rg` for `EndomorphismFibreDoubleCone|exists_interchange` in both source
  roots and `dag/lean_names_upstream.json`: no existing declaration with these
  names. The sibling endomorphism-fibre coordinate-calculus node was read;
  it has no recorded Lean and is not needed to type this item, whose direct
  proof already spells out the same elementary coordinate conventions.

No statement dispute or source fault was found. No new nodes, dependency
modules, or mathematical statement correction are part of the delivery. The only
returned defect H2 is repaired by removing the theorem dependency and using the
Mathlib maps and the own-module sigma_1 helper, as requested.

### Validation

The saved returned packet was first dry-run as requested: preflight and compile
passed (dry-run commit db8edfb6f1e). That mechanical pass did not fix H2;
the repair described above then changed the module, signature record and report.
The revised file passed scompile.py in sandbox and library modes in 6.3 s
and 7.9 s, with no errors or warnings. Preflight and per-file compilation
through deliver2.py are also required before the push. All binders and universes
are explicit, definitions have real data and the single postponed theorem is
`exists_interchange`. No direct Git command or local Lean invocation is used.

## Second reading by Q23

This is the author's second pass with the node and final file open; the
maintainer performs the independent review after delivery. No other agents
were started, as instructed by the dispatcher brief.

I checked Formula by composing e.hom with the four target projections in
order b,b',a,h. Their right sides read b,b',a,-a', respectively. I then checked
InverseFormula in source order b,a,b',a', obtaining b,a,b',-h. All lower
indices in the fourth equations agree because (q-1)+1=q and (q+1)-1=q;
the reindexing proofs do not add hypotheses. This covers the explicit
formula and inverse clauses, beyond merely asserting that some isomorphism
exists.

I rechecked the naturality block against the three source square conditions:
hα and hβ mean the two maps intertwine the endomorphisms, hsq means beta f =
f' alpha. The intermediate hc and hk are conclusions. Mathlib's mappingCone.map expects
upper followed by right = left followed by lower. Its proof arguments are hsq
and hk in the naturality block; coneEnd uses h.symm, while fibreMap uses h.
Both naturality maps remain the prescribed diagonal maps.

For the triangle block, hi asserts that i intertwines t with c, hp that -p
intertwines c with s[1]. The first equation is precisely Phi K(i)=i. The
second uses sigmaOne with coefficients (1,-1) and negative boundaries on both
sides, yielding (-a,a'), rather than the erroneous unsigned boundary.

Finally I read the three Augmentation predicates together with the final
block: all of g,J,J' are chain maps; the hypotheses sJ=tJ'=0 and fJ=J'g are
present; J_C is Mathlib
mappingCone.map applied to the given square; eta,eta',etaC have exactly the
first coordinates J,J',J_C and zero second coordinates. The strict square hs
is asserted, then its induced cone map is exactly the right hand side of the
last identity. These coordinates uniquely determine the maps, so no arbitrary
comparison map has replaced the canonical augmentations. There are no product,
boundedness or epimorphism hypotheses and no element notation in the Lean.
The repair self-check found no mathematical mismatch. I re-read the revised
module against the returned head's clause table: only the constructors changed;
Formula, InverseFormula, Augmentation and all mathematical quantifiers remain
the same. The sigmaOne construction specializes the Stacks 011G/014E signed
shift to exactly 1: the inverse cone shift scales the source summand by -1
and the target summand by 1. These become the first and second fibre summands,
so multiplication by -1 makes (1,-1) in fibre (v,u) order. There is no
remaining SignedCoconeShift import, coneMap/coconeMap wrapper, Arrow.homMk or
reference to coconeCommShift. This is the reviewer's permitted own-module-helper
alternative, not a rebase or unchanged re-push.
