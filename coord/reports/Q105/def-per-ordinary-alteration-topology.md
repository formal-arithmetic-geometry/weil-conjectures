## Worker report

The module `Sheaf.AlgebraicGeometry.OrdinaryAlterationTopology` defines the ordinary
alteration topology and the marked predicate `AlgebraicGeometry.OrdinaryAlteration.U`.
It contains five definitions, no theorem, no axiom and no `sorry`. The item's node
changes only in `lean`. No new nodes, dependency repairs or statement correction.

Sources read: ILO, Travaux de Gabber, Exposé II 1.1.9--1.2.3, 2.1.1 and
2.3.1--2.3.3, printed pp.24--28, and VII Theorem 1.1, printed p.81, in the
local PDF. The category is II 1.2.2; II 1.2.3 says all its morphisms are maximally
finite dominant. Thus parameter 1 in II 2.3.1 requires just proper surjective
morphisms. II Remark 2.3.2 explains why generators are saturated by taking the
least Grothendieck topology rather than called a pretopology immediately.
VII 1.1 supplies only the notation for the desired cover: this definition does
not assert uniformization or add quasi-excellence as a hypothesis. Read also the
current blueprint ancestor `lem-per-artin-gabber-affine-curve.proof.md`, Step 3;
the inherited auxiliary definition is not itself a blueprint unit statement.

Clause-by-clause rendering:

- A Noetherian scheme `S` is `(S : Scheme.{u}) [IsNoetherian S]`. Mathlib's
  Noetherian class means locally Noetherian and compact; its theorem
  `isNoetherian_iff_of_finite_iSup_eq_top` gives the node's finite affine-cover
  formulation with Noetherian rings.
- The category is exactly the recorded `PrimeToEllAlteration.Alt S`; no category
  is copied. Its full-subcategory predicate on `Over S` is
  `LocallyOfFiniteType T.hom ∧ QuasiCompact T.hom ∧ IsReduced T.left` followed by
  the generic-point condition. For each `t`, the condition that
  `closure ({t} : Set T.left) ∈ irreducibleComponents T.left` implies the same
  condition on `T.hom t` and `(T.hom.residueFieldMap t).hom.Finite`.
  This renders finite type, reduced source, every component generic point,
  generic image, and finite residue extension. Morphisms are precisely
  `Over` morphisms through the existing full-subcategory category instance.
- `IsEtaleCoveringPresieve R` requires `Etale f.hom.left` for every arrow in `R`
  and, for every target point `t`, a member `f` of `R` and a point `v` with
  `f.hom.left v = t`. This is jointly surjective, with no residue-degree condition.
  Presieves allow all families without restricting their index universe; every
  presieve is the presieve of its own family of arrows.
- `topology S` is `sInf` over all Grothendieck topologies making
  `Sieve.generate R` cover for those étale presieves, and making
  `Sieve.generate (Presieve.singleton f)` cover whenever
  `IsProper f.hom.left` and `Surjective f.hom.left` hold. Mathlib computes
  intersections pointwise (`GrothendieckTopology.mem_sInf`), so this is the
  smallest topology specified, with no additional generators.
- Mathlib's `Sieve.generate` closes a family under precomposition. In
  `IsCoveringFamily V f`, `Sieve.ofArrows V f ∈ topology S T` means exactly that
  the arrows factoring through a member form a covering sieve.
- Refinement is already exactly `PrimeToEllAlteration.Refines A a B b` in the
  imported dependency: `∀ i, ∃ (j) (h : A i ⟶ B j), h ≫ b j = a i`.
  Applied to `baseObject S`, these are precisely the node's S-morphisms
  `A_i → B_j`. It is reused, not redefined.
- For `U`, reducedness is `[IsReduced S]`. The argument
  `Z : TopologicalSpace.Closeds S` is a closed subset, and
  `_hZ : interior (Z : Set S) = ∅` means nowhere dense because `Z` is closed.
  No scheme structure on `Z` is requested or chosen.
- `baseObject S` is the actual identity `Over.mk (𝟙 S)` in `alt/S`. Its
  finite-type, quasi-compact and reduced proofs use existing instances.
  Its generic-point condition is the identity, and finiteness of the residue
  map is transported from `RingHom.Finite.id` along `Scheme.residueFieldMap_id`.
  There is no arbitrary object, map or choice in this construction.
- The `∃ (n : ℕ) (T : Fin n → Alt S) (f : ∀ i, T i ⟶ baseObject S)`
  gives a finite family of alterations of S; `IsCoveringFamily T f` says it is
  an ordinary alteration cover. Reindexing by `Fin n` represents every finite
  family, including the empty one.
- Each source satisfies `IsIntegral (T i).obj.left`, which includes nonemptiness
  and the integral-scheme condition, `IsRegularScheme (T i).obj.left`, and
  `IsNoetherian (T i).obj.left`. All three clauses are explicit; no properness,
  connected-component choice, prime, or invertibility condition is added.
- For each source, `∃ H : (T i).obj.left.IdealSheafData` and
  `IsStrictNormalCrossingsBoundary H` reuse the recorded boundary definition.
  The equality `((f i).hom.left ⁻¹' (Z : Set S)) = (H.support : Set (T i).obj.left)`
  is the required set-theoretic inverse-image equality, not an equality of
  subschemes. The existing boundary predicate permits zero components.

Dependency declarations read and used (including their full signatures and docstrings):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; through
  `Mathlib.AlgebraicGeometry.Noetherian`, `IsNoetherian` and its finite affine
  cover characterization.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `LocallyOfFiniteType`, `QuasiCompact`, in the reused category and identity object.
- `Mathlib.AlgebraicGeometry.Properties`: `IsReduced`, `IsIntegral`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`, in the existing category.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Scheme.residueFieldMap_id`.
- `Sheaf.CategoryTheory.Sites.GrothendieckTopos`: its docstring explicitly delegates
  sieves and Grothendieck topologies to Mathlib; the module publicly imports that
  interface. Used `CategoryTheory.Presieve`, `Sieve`, `GrothendieckTopology`,
  `Sieve.generate`, `Sieve.ofArrows` and the topology infimum.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`,
  the dependency's recorded locally Noetherian plus stalkwise regular form.
- `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`:
  `AlgebraicGeometry.IsStrictNormalCrossingsBoundary` and `IdealSheafData.support`.
- `Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology`:
  `AlgebraicGeometry.PrimeToEllAlteration.Alt` and `.Refines`.

Edge cases checked before writing and reread afterward:

- Empty S: `n = 0` is allowed. The empty presieve on the empty base is jointly
  surjective vacuously and therefore a generator, so this allows the empty cover.
  There is no `Nonempty S` binder.
- Nonempty S: the definition requires an actual covering sieve and does not
  declare an empty family covering by convention. Every source that occurs is
  nonempty because `IsIntegral` includes `Nonempty`.
- Empty Z: equality asks for an empty boundary support. The recorded strict
  normal crossings predicate allows its empty component family.
- Reducible reduced S: the existing category tests generic points of every
  component; no integrality of S is assumed. Only the covering sources are integral.
- Nonreduced Noetherian S: the topology is still defined; only `U` and the
  identity base object require reducedness, exactly as in the node.
- Positive characteristic, including characteristic equal to any prime, is
  unrestricted. All definitions have no prime, invertibility or degree restriction.
- Arbitrary family index sizes use `I : Type w`, independent of `u` for covering
  families; presieve generators do not discard larger indexed families.

Searches run with `batch2/msearch.py Q105 def-per-ordinary-alteration-topology`:

- LeanFinder: `Ordinary alteration Grothendieck topology generated by etale covers
  and proper surjective morphisms on reduced generically finite schemes`.
  Eight hits, principally `Scheme.etaleTopology`, `smallEtaleTopology`,
  `jointlySurjectiveTopology`, `etalePretopology` and `grothendieckTopology`.
  They have a different category or lack precisely the ordinary generators.
- Loogle: `"alteration"`: zero hits.
- Mathlib grep: `alteration|ordinaryAlteration|OrdinaryAlteration`: zero hits.
- LeanSearch: `ordinary alteration topology and regular finite covering with
  strict normal crossings boundary`: eight hits (Zariski/étale topologies,
  categorical regular/coherent topologies, and `smallGrothendieckTopology`),
  none defining the node's category/topology or marked predicate.
- `rg -n` over `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `ordinaryAlteration|OrdinaryAlteration|` plus
  `alterationTopology|IsUniformiz|def-per-ordinary-alteration-topology`: zero hits.
  Further source grep for the proposed helper names found only unrelated
  `baseObject` and `U` declarations in different namespaces. The required
  `grep -rn def-per-ordinary-alteration-topology lean/WeilConjectures` had zero hits.
  Read the existing prime-to-ell alteration and strict-boundary modules rather
  than duplicating their notions. Read Mathlib `Sites/Grothendieck.lean` and
  `Sites/Sieves.lean` for infima and generated sieves.

Validation: prescribed `scompile.py` compiles the module cleanly in both sandbox
and library modes, with no warning. The first compile only exposed the reducibility
needed by identity-map instances; explicit `inferInstanceAs` terms and the explicit
residue-field argument repaired it without changing any statement. No node fault or
`STATEMENT-DISPUTED` issue was found.

## Second reading by Q105

This is the delivering worker's second pass, not a claim of an independent worker
review; the dispatch brief forbids starting other agents and assigns independent
review to the maintainer. Reopened the final module and node and checked each
clause against the mapping above. The main semantic checks were that the topology
is on the existing `Alt S`, its generators have no prime-to-ell restrictions,
refinement is reused verbatim, and the marked predicate uses the identity target
and equality of supports. The closed-subset argument plus empty interior matches
nowhere dense closed Z. `IsIntegral` supplies the nonempty clause, while regularity
and Noetherianity are separately retained. Zero covering members and zero boundary
components are both admitted. No semantic mismatch or additional change was found.

The first delivery dry run found a metadata signature mismatch at the leading
`noncomputable` modifier. Moved the modifier to `noncomputable section` and
recorded the literal signature beginning at `def`; no definition body changed.
