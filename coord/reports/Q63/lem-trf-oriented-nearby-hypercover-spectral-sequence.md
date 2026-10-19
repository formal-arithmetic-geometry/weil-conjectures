## Worker report

The main module `Sheaf.Paper.OrientedNearbyHypercoverSpectralSequence` states
`AlgebraicGeometry.OrientedNearbyCycles.Hypercover.exists_descent`. Its proof is `sorry`.
The original node statement is unchanged. Its only changes are the Lean record and the
addition of the definition node described below to `stmt_deps`.

Hypothesis and conclusion audit:

- Noetherian S is `[IsNoetherian S]`. Mathlib defines this as locally Noetherian plus
  compactness, thus using the recorded meanings of pqf-def-locnoeth and quasi-compact
  scheme. Finite presentation of f is the three binders
  `[LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]`, as required by
  the scheme-conventions node (Stacks 01TP).
- The coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`, in the recorded
  bounded-constructible coefficient universe. The integer is `m : ℤ`. The equation
  `hmΛ : (m : Λ) = 0` says exactly that m annihilates the ring; it therefore annihilates
  every Λ-module. `hmS : IsUnit (m : Γ(S, ⊤))` says m is invertible on S.
- `Y : SimplicialObject (Over X)` is an augmented simplicial scheme. The recorded
  `hY : IsProperHypercover Y` requires the limits of all proper-face matching diagrams
  and proper surjectivity of their canonical matching arrows, including the
  augmentation in degree zero. `hfp` explicitly gives the three finite-presentation
  properties for every structural map `epsilon Y i ≫ f : Y_i → S`.
- `K : EtaleDerived X Λ` is the actual unbounded derived category used by the recorded
  nearby-cycle functor. `hK` applies the recorded
  `Etale.DerivedCategory.isBoundedConstructible` to K after the canonical exact
  site-and-scalar transport `readModules X Λ`. The ring `Coeff Λ` is the recorded
  canonical ULift of Λ. Neither a replacement constructibility predicate nor an
  arbitrary equivalence is used. Restriction by `realizationRingIso`, the recorded
  constant-ring module restriction, and AsSmall.up retain the module action and read
  precisely the same étale sheaf. Exactness makes this transport commute with homology.
- `c : ℤ` and `hc` assert H^j(K)=0 for every j<c, with no lower-bound normalization.
- In the definition module, `epsilon` is exactly the structural arrow of the degree-i
  slice object; `coefficient` is its recorded exact inverse image of K. `orientedEpsilon`
  is `squareModules f (epsilon_i ≫ f) epsilon_i (𝟙 S) ...`, using the recorded universal
  oriented square lift. Thus `term f Y Λ K i` is exactly
  R barepsilon_i,* R Psi_(f_i) epsilon_i^*K.
- `Descent.sequence` is Mathlib's `CohomologicalSpectralSequence` starting on page 1:
  its r-th differential has bidegree (r,1-r), and its transitions identify page
  homology with the next page. `Descent.first` identifies E_1^{i,j} with H^j(term_i).
  `support` gives the region i≥0,j≥c on every page, not just on page 1.
- `filtration`, `top`, and `bottom` give an actual decreasing subobject filtration of
  H^n(R Psi_f K). It is full at 0 and zero at max(0,n-c+1).
  `graded` identifies F^p/F^(p+1) with E_r^{p,n-p} at r=max(1,n-c+2), for exactly
  0≤p≤n-c. This page is stationary: every incoming differential has first index
  p-r<0 and every outgoing one has second index n-p+1-r<c. Consequently these are
  E_infinity, with no upper bound on the vertical complexes assumed.
- `augmentation` is the adjoint of the recorded beta for the degree augmentation.
  Mate pasting identifies it with Rpsi_f applied to the ordinary descent unit,
  followed by normalized derived-composition comparison. `edge_first` fixes the
  augmented edge on page 1 to its cohomology map. `edgeCycles`, `edge_cycles`, and
  `edge_next` make this augmentation a surviving edge on every page; `edge_graded`
  identifies it with the stable filtration quotient.
- `Change` quantifies over every Cartesian base change, using the actual Cartesian
  square, a simplicial natural transformation, and Cartesian degree squares. The
  primed base has no Noetherian, finite-type, dimension, or goodness assumption.
  Every ordinary scheme base change gives such data by taking its fibre products.
- The conclusion chooses descent data `Db` for all these base changes, comparisons
  from D, and comparisons for every successive base change `Between b₁ b₂`.
  `Comparison.pages` is a genuine morphism of spectral sequences after exact inverse
  image. `Comparison.first` fixes its first page to the canonical ordinary base-change
  map for barepsilon_i followed by the recorded beta_i; `termChange` constructs this
  mate explicitly, using the unique projection-compatible rectangle comparison.
  `abutmentChange` is the exact-inverse-image homology comparison followed by beta_f.
  `Comparison.edge` is the augmentation square. `steps_comm`, `quotient_comm`, and
  `convergence` express naturality of the finite filtration and its associated graded.
  The successive coefficient identification is `Between.coefficients`, constructed
  from normalized exact inverse-image composition, not supplied as an extra hypothesis.
  Spectral-sequence maps with a fixed first page are unique by induction using the
  page-homology isomorphisms. Identity and composite base changes therefore agree under
  the canonical pullback identifications, by the usual mate-pasting identities.

Recorded dependencies used:

- `Sheaf.Paper.OrientedNearbyCycles`: `EtaleDerived`, `VanishingDerived`, `Coeff`,
  `etaleDatum`, `vanishingDatum`, `etaleModules`, `squareModules`, `nearbyCycles`,
  `baseChange`, `squareLift`, `squareDirect`, `etaleComposition` and their adjunctions.
- `Sheaf.AlgebraicGeometry.ProperHypercover`: `AlgebraicGeometry.IsProperHypercover`.
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`. Its current server
  source was read with `scompile.py --source`, as it is absent from the older checkout.
- `Mathlib.Algebra.Homology.SpectralSequence.Basic`: `CohomologicalSpectralSequence`,
  `SpectralSequence.Hom`; `WeilConjectures.CategoryTheory.Abelian.Filtration`:
  `DecreasingFiltration` and `gr`, read from the current server source.
- Mathlib Noetherian, finite-presentation, quasi-separated, proper, underlying-map and
  simplicial-object declarations supply the recorded scheme and simplicial notions.
- `CategoryTheory.constantRingModuleRestriction` and `realizationRingIso` provide the
  existing fixed-ring scalar transport, imported from their owning modules
  `Sheaf.CategoryTheory.ConstantRingModuleSheaves` and
  `Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor`. Continuity of
  AsSmall.up is Mathlib's dense-subsite instance for `AsSmall.equiv` with the induced
  topology (`etaleTopology X` is that induced topology); no continuity declaration is
  introduced.
- Already stated proof dependencies are imported without `public`: right-derived
  negative vanishing, Grothendieck module sheaves, derived pushforward composition, and
  Mathlib adjunction mates. The DAG proof dependencies for total-site augmentation,
  proper-hypercover descent and composition-adjunction normalization currently have
  no Lean records; their proof plans are included in the theorem docstring. No
  existence of any of these theorems is assumed as a hypothesis of the statement.

Edge cases checked: negative c, n<c (top and bottom then force the entire cohomology
sheaf to vanish), n=c (one graded piece and F^1=0), empty schemes and empty primed bases,
zero K, the zero ring, and m=0 when the base is empty. No positivity or nonzero-ring
hypothesis is added. Degree-zero matching is retained. All simplicial degrees occur,
with no truncation, splitting, etaleness, or uniform upper amplitude restriction.

Searches performed using the prescribed msearch wrapper:

- LeanFinder: "Proper hypercover descent spectral sequence for nearby cycles on an
  oriented vanishing topos" returned ordinary one-hypercover sheaf statements only.
- Loogle: "CategoryTheory.SpectralSequence, AlgebraicGeometry.IsProperHypercover"
  returned no hits (the latter is a project declaration).
- Mathlib grep: "nearby.?cycle|vanishing.?topos|hypercover.*spectral" in
  AlgebraicGeometry returned no hits.
- LeanSearch: "Finite filtration convergence and base change of the augmented spectral
  sequence for nearby cycles of a proper hypercover" returned filter-theory and
  ordinary finite-morphism base-change statements, not this construction.
- Loogle: "CategoryTheory.CohomologicalSpectralSequence,
  CategoryTheory.DecreasingFiltration" returned no hits (filtration is upstream-only).
- Mathlib grep: "hypercover|nearbyCycles|oriented.*[dD]escent" in AlgebraicGeometry
  returned ordinary zero/one-hypercovers of étale sites, not nearby-cycle descent data.
- `rg` in the prescribed upstream WeilConjectures tree found no nearby-cycle/vanishing
  topos implementation and no occurrence of this item id. `rg` in lean/Sheaf found the
  already recorded OrientedNearbyCycles construction but no descent spectral sequence
  or datum. Name searches for the new rectangle, exact-image and descent names found
  no declarations. DAG grep found related total-site and proper-hypercover statement
  nodes, not the newly introduced data package. `blueprint_refs.py search hypercover
  spectral` returned zero blueprint matches; `search hypercover descent` returned four
  finite-hypercover limit/descent items with a different statement.

No statement dispute or correction is needed. No dependency record is replaced.

## New nodes

`def-trf-oriented-hypercover-descent-datum`, module
`Sheaf.Paper.OrientedHypercoverDescentDatum`, packages the missing augmented finite
nearby-cycle descent data and their canonical base-change comparisons. Its definitions
use the recorded nearby functor, actual module inverse images, Mathlib spectral
sequences, and the recorded decreasing filtration. It supplies the canonical scalar/site
reading functor, component augmentation, uniquely projection-normalized oriented
rectangle, and uniquely scalar-insertion-normalized pullback composition. The only
postponed helper laws are `readModules_exact`, `rectangle_existsUnique`, and
`pullComposition_existsUnique`; each is stated by the new node and has its source and
complete mathematical proof in its docstring. Their data are either explicitly
constructed or selected from a uniqueness characterization. `Descent` and `Comparison`
are structures, not existentially chosen definitions. No proper descent datum is
constructed using an unproved existence theorem. The source is Orgogozo §9.2, Stacks
0D7F/0D99/0E46/0E47 and ILO XI Theorem 1.4, §1.9. The real search records are preserved
verbatim in this node's mathlib_searches; the DAG, upstream and project searches above
exclude an existing owner for this particular package.

## Second reading by Q63

Q63 reread both modules against the original node and the new definition node after
elaboration. This is a worker self-audit; the independent delivery review belongs to
the maintainer, as the launch brief specifies. The audit checked the complete hypothesis
and clause mapping above, especially the canonical mate directions, arbitrary primed
bases, n<c, and composition of coefficient pullbacks. It found and repaired missing
explicit site/coefficient universe annotations, the parenthesization of the graded
isomorphism binders, and the n-0 transport in the stable edge square. The finite
filtration uses existing DecreasingFiltration rather than a new filtration notion.
The main theorem has no extra base-change isomorphism or Psi-goodness hypothesis.

Validation: scompile.py compiled both delivered modules separately, including the private
side overlay, sandbox probes and library paths, with no errors or warnings. The definition
module took 25.6 s in the private overlay and 16.2 s at its library path; the main theorem
took 51.7 s at its library path, within the required 60-second per-file limit.

## Maintainer review fix (cc review service)

The definition module no longer imports `Sheaf.Paper.PsiGoodOrientedCohomologyStrata`.
That module belongs to lem-trf-psi-good-oriented-cohomology-strata. Its proof
dependency lem-trf-psi-proper-surjective-constructibility uses this item as a proof
dependency. The import therefore inverted the DAG and would close the import cycle
Strata -> PsiProperSurjective -> this item -> DescentDatum -> Strata when the stage-2/3
proof-dependency imports are added. The import was used only for the instance
`PsiGoodStrata.upContinuous`. `readModules` now obtains that instance locally by
`inferInstanceAs` from Mathlib's `Equivalence` dense-subsite instance for
`AsSmall.equiv`. It imports `realizationRingIso` and `constantRingModuleRestriction`
from their owning modules. No statement, declaration name or record changed. Both
modules compile cleanly with tools/nt_compile.py --json.

