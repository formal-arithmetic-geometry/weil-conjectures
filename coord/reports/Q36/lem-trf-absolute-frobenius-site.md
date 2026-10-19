## Worker report

Item: `lem-trf-absolute-frobenius-site`, stage 2, Q36, 2026-10-17.

The previous stale-assignment diagnosis confused a stage-1 completion with a
stage-2 completion. Q09 split and reviewed the DAG proof; the current node has
no `lean` record. This packet states it, without changing its natural-language
statement, dependencies, proof, or any target. No statement dispute was found.

The main module is `Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite`, with theorem
`AlgebraicGeometry.Scheme.absoluteFrobenius_proEtale_trivialization`. Its only
proof is `sorry`. Two real helper definitions implement exact descent of an
ordinary module natural isomorphism and its composition comparison. They use
`Functor.mapDerivedCategoryNatIso`, `mapDerivedCategoryIdIso`, and
`mapDerivedCategoryCompIso`; their data contain no postponed proof or choice.

Hypotheses and clauses, matched individually:

- Scheme: the family quantifies over `X : Scheme.{u}`. This is Mathlib's scheme,
  not an affine, finite-type, Noetherian, separated, or nonempty specialization.
- Characteristic `p > 0`: `p : ℕ`, `hp : Nat.Prime p`, and
  `hX : X.IsCharacteristic p`. The recorded predicate says that `p` vanishes
  on EVERY open; the Frobenius construction uses its consequence `hX.2 ⊤`.
  Primality is the convention of the characteristic dependency, and implies
  positivity. No `CharP` instance excluding the empty scheme is required.
- Coefficients: `(A : Type u) [CommRing A]` is arbitrary. There is no
  finiteness, nontriviality, torsion, invertibility, boundedness, or completion
  hypothesis. This renders the arbitrary constant coefficient ring used in
  step 5 of the node's proof. `proEtaleConstantRing X A` is exactly the
  sheafified constant CommRingCat coefficient sheaf used by the recorded
  `proEtaleDerivedCategory X A`, with the same canonical ULift.
- Small pro-etale site: `X.ProEt`, `proEtaleBaseChange`, and
  `proEtaleRingModules X (proEtaleConstantRing X A)` use the published original
  small site. Its objects have universe `u+1`, its morphisms universe `u`, and
  its module values universe `u+1`. No equality of these universes is imposed.
- Absolute `p`-power Frobenius: `X.iterateFrobenius hp (hX.2 ⊤) 1`.
  The family treats every `n : ℕ`, with `n` meaning the `p^n`-power iterate,
  exactly as `def-weil-absolute-frobenius-scheme` specifies.
- Canonical choice: `r X hX n` is an isomorphism from the identity of the site
  to base change. Its underlying first projection is the actual absolute
  Frobenius of the test object, not an unspecified automorphism. The second
  projection equals its structure map because the component is a site
  morphism. The bound `hV` states vanishing of `p` on its global sections and
  is proof data only. These two projections uniquely characterize relative
  Frobenius in the chosen variable-factor-first pullback.
- Canonical module map: the displayed sectionwise unit equation says
  `unit_M ≫ pushforward(tau_M) = M(r_V.inverse)`. It uses the already
  tensor-unit-normalized `proEtaleRingModuleAdjunction`. The adjunction Hom
  bijection uniquely determines `tau`, including its scalar action; this is
  not bare existence of an arbitrary natural isomorphism.
- Derived trivialization: `proEtaleFrobeniusDerivedIso A (tau X hX 1)` has
  source `proEtaleConstantRingDerivedPullback A F_X` and target the identity
  on EXACTLY `proEtaleDerivedCategory X A`. Its data are the termwise descent
  of `tau`, followed by the canonical derived identity comparison. Thus the
  existential module isomorphism in the theorem supplies the required
  canonical derived isomorphism without another choice or assumption.
- Restriction to EVERY open: the clause quantifies over `U : X.Opens` and
  supplies its characteristic proof and the actual equality
  `F_U^n ≫ U.ι = U.ι ≫ F_X^n`. The equality of natural transformations is the
  square from `LF_X^* ⋙ Lj^*` through inverse composition, this equality of
  scheme maps, and forward composition to `Lj^* ⋙ LF_U^*`. It identifies
  `tau_X` restricted to `U` with `Lj^*(tau_U)`. Both functor unitors are
  included, rather than identifying composite functors silently.
- Multiplicative iterates: for ALL `a b : ℕ`, the actual scheme equality
  `F_X^a ≫ F_X^b = F_X^(a+b)` transports the derived functor. The equation
  identifies `tau_(a+b)` with the canonical composition comparison, followed
  by `L(F_X^b)^*(tau_a)` and then `tau_b`. This is the node's equation with
  the two arbitrary exponents interchanged; they range independently over
  all naturals. In particular it includes the iterated `p`-power map.
- Zero iterate: the final clause identifies `r_0` with the inverse of the
  canonical `pullbackId`, after the actual equality `F_X^0 = id`. Together
  with the SAME module unit normalization and exact descent, this fixes
  `tau_0` to the canonical identity-pullback trivialization. Neither the
  identity nor a zero-exponent case is discarded.
- The `comp` family appearing in those equations is fixed, for every pair
  of morphisms, by the section map of fibre-product pasting under
  `conjugateIsoEquiv` for the actual module adjunctions. The normalization
  is exactly the section normalization in the published pro-etale derived
  composition theorem. Hence the equations use canonical comparisons,
  not comparisons chosen to make the equations hold.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its `Hom`.
- `Sheaf.AlgebraicGeometry.SchemeCharacteristic`:
  `AlgebraicGeometry.Scheme.IsCharacteristic`.
- `WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius`:
  `AlgebraicGeometry.Scheme.iterateFrobenius`, including its point and
  section formulas and the vanishing-on-opens lemma.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations`:
  the recorded operations interface was read in full; its coefficient
  restriction is repaired as described below. That interface is reexported.
- `Sheaf.AlgebraicGeometry.ProEtaleOperations` and
  `ProEtaleOperationsCanonicalAdjunction`: `proEtaleRingModulePullback`,
  `proEtaleRingModuleDirectImage`, `proEtaleRingModuleAdjunction`, their
  exactness instances and `proEtaleRingDerivedPullback`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `proEtaleBaseChange`, `proEtaleConstantRing`, and the constructed
  `proEtaleCoefficientInverseImageMap`. No private copy of an inverse
  image, scalar map, module category, or localization is introduced.

Already stated proof-dependency modules are imported without `public`:
absolute Frobenius well-definedness, weakly etale universal homeomorphisms,
weakly etale localization, the selected canonical pullback composition,
the recorded intrinsic realization transport, and K-flat resolutions.
The relative-Frobenius universal-homeomorphism proof dependency presently
has no statement module and therefore cannot yet be imported. This does not
obstruct the present statement; its geometry is documented in the theorem's
seven-step proof docstring. Mathlib proof ingredients (fibre products,
sheafification, adjunction mates, localization, and weakly etale base change)
are supplied by the imported interfaces.

Edge cases checked before settling the signature: the empty scheme has the
recorded characteristic for every prime; its global and empty-open section
rings may be zero. No nontriviality assumption excludes them. The empty open
and the full open are both quantified over. The zero coefficient ring is
allowed. `n=0`, `a=0`, and `b=0` occur explicitly. Imperfect fields and
nonreduced schemes are permitted: absolute Frobenius need not be a scheme
isomorphism; only relative Frobenius on WEAKLY ETALE objects is asserted
invertible. In particular the statement applies to Spec F_p[epsilon]/epsilon²
and imposes no perfection or finite-type assumption. No condition on the
cohomological degrees of the input is present.

Searches for an existing statement (2026-10-17):

- `msearch.py`, LeanFinder, query `canonical trivialization derived pullback
  absolute Frobenius small pro-etale site`: eight hits, all étale-category
  constructions or étale morphism infrastructure. None is this theorem.
- `msearch.py`, Loogle, query `"frobenius", "pullback"`: only
  `CategoryTheory.Regular.frobeniusMorphism_isPullback`, a regular-category
  Frobenius law unrelated to scheme Frobenius.
- `msearch.py`, LeanSearch, query `canonical trivialization of derived
  pullback along absolute Frobenius on pro-etale sheaves`: fibre-bundle
  trivializations and generic `SheafOfModules.pullback`; no matching theorem.
- `msearch.py`, grep of Mathlib/AlgebraicGeometry, query
  `absoluteFrobenius|relativeFrobenius|iterateFrobenius`: zero hits.
- `rg` of the slopmaster2 `WeilConjectures` sources and the current
  `lean/Sheaf` and side `lean/WeilConjectures` sources for Frobenius with
  pullback/site/trivialization found geometric Galois Frobenius transport,
  geometric-fiber formulas, and Frobenius open squares. The geometric
  Galois Frobenius source was opened: it concerns automorphisms after base
  change from finite fields, not absolute Frobenius on arbitrary schemes.
- Searches for this node id in the source library found no existing
  declaration. Searches of the upstream name index, source tree and side
  tree for every newly introduced principal name found no collision.
- Searches for constant-ring pullback/comparison interfaces found the
  object-level `proEtaleConstantModulePullback` and its map, finite-ring
  realization transport, and the isomorphism-only constant comparison.
  None gives the arbitrary-ring canonical coefficient isomorphism needed
  here. The new operations are specializations of the published general
  ring-sheaf functors, not reimplementations of their data.

Source checked: the current main-20261015 statement, all seven current DAG
proof steps, and Stacks `more-morphisms.tex`,
`lemma-relative-frobenius-weakly-etale` (Tag 0F6W). The Stacks lemma applies
to every weakly etale object, with no finiteness hypothesis.

Validation: both delivered files compile separately, in dependency order,
through the prescribed `scompile.py` wrapper, with no errors or warnings.
No global build, live source write, direct git command, or push was run.
The prescribed `deliver2.py --no-push` dry run checks the packet before handoff;
the independent second reader handles delivery.

## Dependency modules

`def-weil-pbc-proetale-operations`: §1(B) repair in
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`. The recorded
`sfIntrinsicDerivedPullback` takes `[Finite A]`, which would exclude the
arbitrary constant ring in the Frobenius node's proof. The new module
publicly reexports that entire interface and the general identified-ring
operations. It states invertibility of the actual constant-section
coefficient map as a named theorem (with `sorry` and a complete construction
proof docstring), turns precisely that map into an isomorphism via `asIso`,
and specializes the existing ring-module pullback, direct image, normalized
adjunction, and exact derived pullback. The output derived category is the
recorded intrinsic `proEtaleDerivedCategory`, definitionally. The zero ring
and every coefficient ring in the prescribed universe remain allowed.
Only this dependency's `lean` field is changed; the required explanation
is also in `lean.note`. No new nodes or natural-language corrections occur.

## Second reading by Q36

Independent second reader, 2026-10-17. I opened the current DAG node, its
seven proof steps, both delivered modules, every statement-dependency node,
and their declaration sources. Verdict: the Lean states the node, including
its canonical normalization and both compatibilities. No statement correction,
new node, target change, or mathematical signature change is needed.

The source statement was read first in the main-20261015 blueprint and its
proof, then in `more-morphisms.tex`, the weakly etale section and
`lemma-relative-frobenius-weakly-etale` (0F6W). The section assumes no
Noetherian, finite-type, separated, affine, perfection, or nonemptiness
condition. Its lemma assumes exactly weakly etale over a characteristic-p
scheme. I also read `sites-modules.tex`,
`lemma-adjoint-push-pull-modules`, and the operations blueprint source.

Object/hypothesis/conclusion inventory and item-by-item match:

1. **An arbitrary scheme X.** Rendered by `X : Scheme.{u}` throughout
   `absoluteFrobenius_proEtale_trivialization`. Mathlib's `Scheme` extends
   `LocallyRingedSpace` by the local-affine condition and `Scheme.Hom` is a
   locally ringed space morphism; I read those declarations in Scheme.lean.
   There are no additional geometric instances. Verdict: exact.
2. **Characteristic p > 0.** `p : ℕ`, `hp : Nat.Prime p`, and
   `hX : X.IsCharacteristic p`. I read SchemeCharacteristic.lean: the
   predicate is `Nat.Prime p ∧ ∀ U : X.Opens, (p : Γ(X,U)) = 0`.
   The dependency explicitly defines characteristic for primes. The
   separately named `hp` is the same proof requirement, not a restriction
   of the characteristic predicate. `hX.2 ⊤` supplies global vanishing
   to upstream Frobenius. Verdict: exact, including the empty scheme.
3. **The small pro-etale site of X.** `X.ProEt` and `proEtaleBaseChange`
   use Mathlib's `MorphismProperty.Over @WeaklyEtale ⊤ X`. I read
   Sites/Proetale.lean and the actual `Over.pullback` definition:
   its value on V has scheme `pullback V.hom f` and structure map
   `pullback.snd V.hom f`. Objects lie in u+1, morphisms in u.
   `ProEt.topology` is the published topology, not an etale replacement.
   Verdict: exact bounded-object site and coefficient size convention.
4. **Absolute p-power Frobenius F_X and its iterates.** The morphism is
   `X.iterateFrobenius hp (hX.2 ⊤) n`, with F_X at n=1. I opened
   upstream AbsoluteFrobenius.lean: it has actual identity-on-points data,
   and its section homomorphism is `s ↦ s ^ p ^ n`. The later Noetherian
   theorem in that file does not impose instances on this definition.
   Verdict: the dependency's absolute Frobenius, including n=0.
5. **Canonical site trivialization.** The family `r` is an isomorphism
   `𝟭 X.ProEt ≅ proEtaleBaseChange F_X^n`. Its displayed first-projection
   equation is F_V^n. Its second projection is V.hom by the over-category
   morphism condition, since the target structural map is pullback.snd.
   Thus it is precisely `(F_V^n,v)`, not an arbitrary isomorphism of site
   functors. The existential `hV` is only a vanishing proof and introduces
   no hypothesis. Verdict: the relative Frobenius used in the source proof.
6. **Derived pullback has a canonical trivialization.** A is an arbitrary
   `(A : Type u) [CommRing A]`, as in proof step 5, with no Finite,
   nontriviality, torsion, or completeness assumption. The `tau` family
   gives `proEtaleConstantRingPullback A F_X^n ≅ 𝟭 _`; its unit equation
   on every M,V,m fixes it as the adjoint mate of `M(r_V.inverse)`.
   The dependency's normalized module adjunction was read, including its
   tensor-unit normalization, so this is a unique specified map rather
   than bare Nonempty data. `proEtaleFrobeniusDerivedIso A (tau X hX n)`
   descends this exact functor isomorphism termwise and uses the derived
   identity comparison. I read ProEtaleDerivedCategory.lean: the codomain
   is the ordinary unbounded localization of modules over the sheafified
   constant CommRingCat coefficient ring, with canonical ULift. Verdict:
   exactly LF_X^* ≅ id on the recorded derived category.
7. **Commutation with restriction to every open subscheme.** The clause
   quantifies over every `U : X.Opens` and every n, with characteristic
   proof hU and the actual morphism equality `F_U^n ≫ U.ι = U.ι ≫ F_X^n`.
   Starting from `LF_X^* ⋙ Lj^*`, inverse composition, equality transport,
   and forward composition give `Lj^* ⋙ LF_U^*`. Whiskering tau_U then
   agrees with tau_X whiskered by Lj^*, including the correct unitors.
   Restriction along an open is this site pullback, by the imported
   weakly-etale localization interface. Verdict: the canonical restriction
   square, without an extra open or coefficient hypothesis.
8. **Multiplicative iterates, including identity.** For all a,b the actual
   equality `F_X^a ≫ F_X^b = F_X^(a+b)` transports the derived functor.
   The displayed equality trivializes it by the composition comparison,
   `L(F_X^b)^*(tau_a)`, then tau_b. This is the node's composition equation
   with its two universally quantified exponents interchanged. For zero,
   `r X hX 0` is fixed by `pullbackId.symm` and the equality `F_X^0 = id`.
   The same unit equation therefore also fixes tau_0 and its derived
   descent to the canonical identity comparison. Verdict: all iterates,
   not just positive powers or a chosen iterate.
9. **The comparisons in 7 and 8 are canonical.** The family `comp` ranges
   over all scheme morphisms, but is fixed by its displayed section formula
   after `conjugateIsoEquiv` under the actual normalized adjunctions. I
   opened ProEtaleCanonicalPullbackComposition.lean: its direct-image
   normalization is exactly `M.val.map (pullbackComp f g).hom.op`.
   The new `proEtaleFrobeniusDerivedComp` is exact descent of that ordinary
   comparison, followed by `mapDerivedCategoryCompIso`. Thus these are
   the node's composition comparisons; the existential quantifier cannot
   choose different comparisons to force the compatibility equations.

Dependency repair review (H13):

- I opened the complete general `ProEtaleOperations` construction and
  `ProEtaleOperationsCanonicalAdjunction`, and the recorded
  `ProEtaleIntrinsicFiniteOperations`. The last has section variables
  `[Finite A]`, so it cannot be used for this node's arbitrary A.
- The dependency delivery publicly reexports that existing interface and
  the general arbitrary-ring-sheaf operations. It retains the full node's
  module pullback, direct image, exact derived pullback, K-injective
  direct image, and adjunction interfaces. Its additional constant-ring
  abbreviations specialize the actual general operations, with the
  coefficient identification `asIso` of the existing canonical map
  `proEtaleCoefficientInverseImageMap`. No private category or replacement
  inverse-image construction is introduced. The invertibility theorem
  supplies only proof data for this fixed map.
- I read ProEtaleInverseImage.lean down to the model-site module transport,
  the sheafified constant ring, and the two coefficient maps. The new
  specialization uses exactly these definitions. Its HasDerivedCategory
  instance and the recorded intrinsic category are the same standard
  localization. The general reexports retain every clause of the
  dependency node, while its new principal declaration exposes the
  arbitrary-constant-ring case needed here. Its lean.note correctly
  explains both the unusable finite record and the repair.
- There are no new definition nodes to audit (H12). Both node copies
  differ from the shared base only in lean. No statement_change exists
  or is needed, so no citer correction audit is applicable.

Edge cases checked independently: the empty scheme and empty open satisfy
vanishing without a nontriviality hypothesis; U may also be the full open.
The zero coefficient ring is permitted. The n=0, a=0, b=0, and a=b=0 cases
are included. There is no index-family nonemptiness condition. Characteristic
2 and all other primes are covered. Imperfect fields and nonreduced schemes
are included: F_X need not itself be an isomorphism of schemes. Unbounded
complexes and all cohomological degrees are retained. The shared u follows
the recorded bounded-object site convention and does not identify its
object and morphism universes. Different initial scheme/coefficient sizes
can be placed in a common larger ambient universe; no test-algebra
hypothesis becomes vacuous through an independent smaller universe.

Independent searches, using other terms than the worker:

- msearch LeanFinder: `relative Frobenius equivalence weakly etale sheaves
  identity inverse image` returned eight ring-Frobenius/isocrystal hits;
  none concerns scheme site pullback.
- msearch Loogle: `"Frobenius", "iso"` returned five categorical
  Frobenius-morphism and Witt-isocrystal hits, not this statement.
- msearch LeanSearch: `inverse image constant sheaf canonical comparison
  isomorphism` returned IsConstant, concrete sheafification, and continuous
  pushforward congruence declarations. None identifies this coefficient
  map for arbitrary scheme morphisms.
- rg of Mathlib Sites and AlgebraicGeometry, upstream WeilConjectures,
  shared lean/Sheaf, and the exact side pro-etale framework found no
  absolute-Frobenius site trivialization or collision with the new names.
  I read the side ModuleObject/Derived/UpperLowerStar source and the
  framework audit: those are condensed module-object derived operations,
  not this ordinary constant CommRingCat-sheaf module category.
- The closest existing constant-ring theorem,
  `ProEtale.finiteCoefficientCommRingMap_isIso` in ProEtaleConstantExact,
  was opened: it assumes Finite, a discrete topology, and its specific
  continuous-function comparison. `proEtaleIso_constantComparison` was
  also checked and requires IsIso f. Neither covers general f here;
  absolute Frobenius is not in general an isomorphism. The existing
  fixed-scalar constant comparison supplies no second definition of the
  present intrinsic coefficient map or its derived trivialization.

Mismatch and repair: no mathematical mismatch was found. I clarified the
proof docstring of `proEtaleConstantRingComparison_isIso`: it now explicitly
says the coproduct of terminal sheaves is taken on the underlying sheaves
of sets, before finite-product preservation transports the ring operations.
This avoids reading the argument as a coproduct of terminal ring sheaves.
No declaration, definition data, or signature changed.

H5/H6/H8/H9 checks: the two helper isomorphisms are built from the published
exact derived-functor comparisons. Every new definition has real data.
The only two theorem bodies are sorry, each with its source and blueprint
marker and a complete proof description. The main theorem docstring follows
all seven DAG steps. All variables and universes are explicitly bound;
autoImplicit is false. Both recorded lean.statement strings occur verbatim
in their files and every line is at most 100 characters.

Validation: both delivered files compiled separately in dependency order
through scompile.py, exit 0, with no errors or warnings. The final docstring
clarification is recompiled before the required delivery preflight.
