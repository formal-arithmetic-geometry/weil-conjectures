## Worker report

The module `Sheaf.Algebra.Homology.TotalTensorHomotopyConeSigns` states the whole node as
`SheafOfModules.TotalTensorSigns.totalTensorHomotopyConeSigns`, with one `sorry` and no
proved theorem. The auxiliary abbreviations and definition wrappers expose existing constructions; none
constructs a second tensor, quotient, cone, or category. No node correction, dependency
repair, new node, or disputed mathematical statement is needed.

Hypotheses and objects, matched to the node:

- A small site and a commutative ring sheaf are `{C : Type u} [Category.{v} C]`,
  `[EssentiallySmall.{r} C]`, `{J : GrothendieckTopology C}`, and
  `(R : Sheaf J CommRingCat.{r})`. The site object and morphism universes are independent;
  essential smallness in the module universe expresses precisely relative smallness.
  These existing instances supply sheafification, the abelian category and all sums.
- `Modules R` is the dependency's `CategoryTheory.ringedSiteModules.{r}` applied to the
  underlying ring sheaf. Integer cochains are `CochainComplex (Modules R) ℤ`.
  `Homotopy`, `QuasiIso`, `HomotopyCategory`, and `⟦n⟧` are Mathlib's constructions from
  the abstract-derived-category and homotopy-category nodes; no derived localization
  or additional hypothesis on its morphism universe is needed to state this node.
- `tensor R = curriedTensor (Modules R)` uses `cochainModulesMonoidal` and its actual
  sheafified balanced tensor. `total R = (tensor R).map₂CochainComplex` uses the recorded
  direct-sum totalization, with differential `d tensor 1 + (-1)^p 1 tensor d`.
  `((total R).obj A)` is H_A and `((total R).flip.obj A)` is H^A.

Each conclusion, in theorem conjunction order:

1. For every A, `.Additive` for both fixed-factor complex functors, `.Additive` and
   `.IsTriangulated` for their existing quotient functors `homotopyTensor R` at
   `(HomotopyCategory.quotient _ _).obj A`. The quotient bifunctor really is induced
   by these complex maps: it is the upstream `bifunctorMapHomotopyCategory`, constructed
   by `Quotient.lift₂` from total tensor and the two explicit tensor homotopies.
   The two `NatTrans.CommShift` clauses are for the canonical quotient comparison
   isomorphisms. Thus the quotient shifts are the inherited coherent shifts, not
   arbitrary choices of exact structures. On complexes the existing `CommShift`
   instances use exactly `mapBifunctorShift₂Iso` for H_A and `mapBifunctorShift₁Iso`
   for H^A; BifunctorShift supplies their naturality and zero/addition coherence.
2. For arbitrary `f g : X ⟶ Y` and `h : Homotopy f g`, the supplied canonical tensor
   homotopies are `mapBifunctorMapHomotopy₂ (𝟙 A) h` and
   `mapBifunctorMapHomotopy₁ h (𝟙 A)`. The wrappers `homotopyLeft R A h` and `homotopyRight R A h` use these terms
   verbatim, with their endpoint types written explicitly. Their types assert exactly that their endpoints
   are the two tensor images. The wrapper `ι` is the canonical summand inclusion. The displayed `.hom n (n-1)` summand equations assert
   `p.negOnePow • (A.X p ◁ h.hom q (q-1))` and `h.hom q (q-1) ▷ A.X p`.
   `Homotopy`'s commutation equation is u-v=dh+hd, with the source/target compositions
   written in categorical order. The indices p,q,n range over all integers.
3. For every f, `coneLeft R A f` abbreviates `mapBifunctorMappingCone₂Iso A f (tensor R)`;
   `coneRight` abbreviates `mapBifunctorMappingCone₁Iso f A (tensor R)`.
   These are actual chain isomorphisms, with explicit inverse data already constructed
   upstream. There is no existential selection of arbitrary isomorphisms.
4. The two chain equations with `mappingCone.inr f` assert preservation of inclusions,
   hence identity on every target Y summand. The two component equations precomposed
   by `(mappingCone.inl f).v (q+1) q` assert the sign `p.negOnePow` on
   `A^p tensor X^(q+1)` and the unsigned map on `X^(q+1) tensor A^p`.
   The target inclusions in degree n+1 explicitly perform the required reindexing.
5. The next two equations use the negative of `mappingCone.triangle f |>.mor₃`, which
   is precisely the unsigned projection p. They assert
   phi_L followed by p = H_A(p) followed by s²_1 and the analogous s¹_1 identity.
6. The following two equations use `.mor₃` itself, precisely -p. Together with the
   first-arrow tensor maps and the inclusion equations, they identify all three
   tensor-image triangle arrows with those of the cone triangle of the tensor map.
   This convention was read in Mathlib's `mappingCone.triangle` definition, which
   uses `Cocycle.homOf ((-fst f).rightShift 1 0 (zero_add 1))`.
7. The next conjunction quantifies over every strictly commuting square
   `comm : f ≫ b = a ≫ f'`. Its two equations assert naturality of these actual cone
   comparisons with the canonical diagonal `mappingCone.map` for both tensor orders.
8. The swap is `swap R B A`: the existing bicomplex symmetry followed by the signed
   total flip, the exact construction of `CochainComplex.Monoidal.braiding B A`. Its chain-isomorphism
   type includes existence and inverse identities. The equation identifying its
   inverse with `swap R A B |>.hom` gives the same signed swap as inverse. Its
   summand equation is exactly `(i*j).negOnePow • ((β_ (B.X i) (A.X j)).hom ≫ ι)`.
9. The next clause asserts swap naturality in BOTH variables, for arbitrary
   `a : A ⟶ A'` and `b : B ⟶ B'`, using the actual `mapBifunctorMap` on both sides.
10. `IsKFlatIndependentCoefficients A → ...` asserts that both fixed-factor tensor
    functors preserve every `QuasiIso f`, with completely arbitrary X,Y. There is
    no endpoint flatness, K-flatness, boundedness, or cohomology-flatness binder.
    Its second conjunct asserts K-flatness of A[n] for every integer n.
11. The final, separate implication from `∀ i, IsFlatOnSite (A.X i)` asserts termwise
    flatness of every shift. It does not assert that an arbitrary unbounded complex
    of flat terms is K-flat. This is the reading explicitly fixed in the node's
    split_report and its final proof step.
12. Well-definedness on sheaves is built into all the maps above: the existing
    localization tensor is induced by sheafification of sectionwise balanced
    presheaf tensor. The total maps, homotopies, cone comparisons and signed
    braiding are made exclusively from this tensor functor's maps, integer scalars,
    canonical summand maps, and the presheaf-induced symmetry. No arbitrary
    sheaf maps are substituted and no descent assumption is added.

Dependency declarations read and used (the recorded dependency interfaces):

- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`; inherited `SheafOfModules` abelian structure.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  `DerivedCategory` and Q/Qh; its complex, homotopy, shift and cone conventions are
  used here before derived localization. `mappingCone.triangle` comes from
  `Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated`.
- `def-pc-tensor-complex-sheaves`: `Mathlib.Algebra.Homology.BifunctorShift`,
  `CochainComplex.mapBifunctor` and its curried functor `Functor.map₂CochainComplex`.
- `def-weil-triangulated-category`: `Mathlib.CategoryTheory.Triangulated.Functor`,
  `Functor.IsTriangulated`, with the existing Pretriangulated/IsTriangulated structures.
- `lem-weil-pbc-total-tensor-integer-shifts`: the same BifunctorShift module,
  `mapBifunctorShift₁Iso`, `mapBifunctorShift₂Iso`, their component and coherence
  declarations, including `Functor.instCommShift₂IntCochainComplexIntMap₂CochainComplex`.
- `def-pur-sheaf-tensor-product`:
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`,
  `SheafOfModules.cochainModulesMonoidal`, symmetric/preadditive and colimit instances.
- `def-pc-kflat-complex`: `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`,
  `CochainComplex.IsKFlatIndependentCoefficients`, quantifying over every acyclic F
  and using `mapBifunctor F A (curriedTensor _)` in the stated order.
- `def-pc-flat-sheaf-modules`: `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`,
  `SheafOfModules.IsFlatOnSite` (the exactness of `siteSheafTensorRight`).
- `lem-pur-homotopy-category-triangulated`:
  `Mathlib.Algebra.Homology.HomotopyCategory.Triangulated`,
  `HomotopyCategory.instIsTriangulatedIntUp` and cone distinguished triangles.
- The proof-only dependencies are imported as ordinary imports:
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`
  (`SheafOfModules.tensorClosed`),
  `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
  (`PresheafOfModules.sheafification` and its adjunction), and
  `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`
  (`CochainComplex.mappingCone.quasiIso_iff_acyclic`). The tensor construction,
  shifts and homotopy-category dependencies also serve the proof.
- Additional canonical construction APIs reused, not redefined:
  `WeilConjectures.FromJoel.Algebra.Homology.BifunctorTriangulated` and its imports
  (`mapBifunctorMappingCone₁Iso`, `mapBifunctorMappingCone₂Iso`,
  `bifunctorMapHomotopyCategory`, coherent quotient shifts), Mathlib's
  `mapBifunctorMapHomotopy₁`/`₂`, and
  `WeilConjectures.Mathlib.Algebra.Homology.Monoidal`
  (`CochainComplex.Monoidal.braiding`).

Source checks: read sites-cohomology.tex lemma-derived-tor-exact (06YM),
definition-K-flat, lemma-K-flat-quasi-isomorphism (06YP); derived.tex definition-cone,
definition-distinguished-triangle and remark-double-complex-as-tensor-product-of
(0G6E); more-algebra.tex item-shift-tensor (0FNH) and item-flip-tensor-product (0GWR).
Also read the current main-20261015 blueprint's
`lemma-weil-pbc-perfect-projection-formula.proof.md`: its first paragraph uses tensor
exactness for closure under shifts and cones, which this chain-level node supplies.

Edge cases checked before/during formulation:

- Zero A, zero complexes, f=0 and f=identity: the cone isomorphisms keep both summands
  and both triangle signs, rather than merely giving an abstract cone equivalence.
- Negative degrees and negative shifts: `Int.negOnePow`, integer indices and existing
  integer-shift instances retain these cases. For odd p the left cone source sign is
  negative and the right is positive; for even p both are positive.
- n=0 for shifts and n=-1: coherence is the existing all-integer CommShift data,
  not merely a shift-by-one witness. Termwise flatness is reindexing for both signs.
- Empty site and zero ring: no nonempty or nonzero binder is present; sheafification,
  tensors and categorical formulas still apply.
- Arbitrary unbounded complexes and non-K-flat quasi-isomorphism endpoints are retained.
  The sole K-flat hypothesis is on the fixed factor A, and flat terms enter only the
  separate final implication.
- Site object and Hom sizes remain independent u,v, and coefficient size r is only
  constrained by the existing relative-smallness interface. No forced equality u=v.

Searches for an existing exact statement:

- `msearch.py leanfinder`: “Total tensor of sheaf complexes preserves signed homotopies
  cone triangles and quasi isomorphisms for K flat factors”: eight hits, chiefly
  good-tensor predicates, `HomotopyCategory.mappingConeCompTriangleh_distinguished`
  and generic `mappingCone.mapTrianglehIso`; no whole-item match.
- `msearch.py loogle`: `"map₂CochainComplex", "mappingCone"`: zero hits.
- `msearch.py grep` in Algebra/Homology:
  `mapBifunctor.*[Hh]omotop|mappingCone.*[Tt]ensor|[Tt]ensor.*[Kk]Flat`:
  five hits in BifunctorHomotopy, which supply the reused homotopies, not the item.
- `msearch.py leansearch`: “The direct sum total tensor functor on sheaf cochain
  complexes preserves homotopies and mapping cones and K flat complexes preserve
  arbitrary quasi isomorphisms”: eight hits, including preservation of quasi-isos
  by a homology-preserving termwise functor and generic cone comparison, no exact match.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for the node id and tensor/cone/
  homotopy patterns located the reused upstream BifunctorMappingCone,
  BifunctorTriangulated and signed Monoidal APIs. None packages this node's full
  statement. The nearby `KFlatFixedTensorTriangulated` concerns derived descent and
  assumes both flat terms and K-flatness; it does not state the current signed
  homotopy/cone components or the unrestricted fixed-K-flat claim. The new namespace
  and main declaration name have no upstream or project match.
- The example `Sheaf.CategoryTheory.CompactObject` is withdrawn in this checkout;
  read its node and the recorded upstream `WeilConjectures.CategoryTheory.CompactObject`
  instead for the actual declaration/docstring/header conventions.

All compilation uses scompile.py; no shared source, launcher script, or global build is
modified. The final server compilation and delivery preflight are recorded by deliver2.py.

Elaboration repair: initial fully expanded signatures exceeded the fixed 60-second
file limit. Exposed the endpoint types of the existing cone comparisons, homotopies,
shift comparisons and summand inclusions in named definition wrappers. Their bodies
are the original canonical terms, with no choice, new mathematical assumption or
sorry data. `swap` uses precisely the existing bicomplex braiding and signed total
flip, avoiding irrelevant monoidal associativity instance searches on complexes.
The shift wrappers are the exact integer-shift dependency maps. Temporary type
probes live outside the delivered lean/ tree and are not delivered.

Final explicit scompile.py validation: clean exit 0, no warnings; sandbox-name
compilation 43.2 seconds and final-module-name compilation 50.8 seconds, both within
60 seconds. `autoImplicit` is disabled; all universes are declared. The node copy
was compared with the read-only base: its only changed field is `lean`.

## Second reading by Q32

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
