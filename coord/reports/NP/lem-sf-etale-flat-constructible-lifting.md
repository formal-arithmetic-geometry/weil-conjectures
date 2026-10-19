## Worker report

Existing declaration: `AlgebraicGeometry.Etale.liftsAlongEpi_flat_isConstructibleSheaf`,
module `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel`,
source lines 105–140 (theorem begins at line 119). No new module, definition, proof,
or dependency node is supplied. Only the item's lean record is replaced with a complete
existing-declaration record. The statement is unchanged.

The source theorem and its full docstring were read, including the ambient declarations
`universe u`, `variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}`.
Only X occurs in the theorem, so Y is not an additional parameter. The recorded statement
is the source signature verbatim; the ambient parameters are supplied by that module.

Hypothesis and clause comparison:

- Finite commutative ring Λ: ambient `(Λ : Type (u + 1)) [CommRing Λ]` and
  theorem binder `[Finite Λ]`. Neither a field nor a nonzero ring is required.
- Noetherian scheme X: ambient `{X : Scheme.{u}}` and `[IsNoetherian X]`.
- The category C: both object-property arguments explicitly have domain
  `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)`, exactly the category named
  in this node. This uses the constructible-material encoding, not the alternative
  constant-ring-sheaf `SheafOfModules` encoding.
- Constructible means the source predicate: the source and target properties use
  `AlgebraicGeometry.Scheme.IsConstructibleSheaf`, from
  `WeilConjectures.ConstructibleSheaf.Defs`. Its `exists_stratification` field
  quantifies over `Scheme.Stratification X` and asks for
  `IsFiniteLocallyConstantSheaf ((Etale.upperStar _ (S.immersion i)).obj F)`
  on every stratum. The source docstring requires constructible locally closed strata;
  finite locally constant extends local constancy and `IsFiniteSheaf`, whose geometric
  fibers are finitely generated. This is exactly the source predicate explicitly chosen
  by the node, and is not the set-valued predicate from the general sheaf dependency.
- Every epimorphism p:A→B, every g:G→B, and constructibility of G: unfolding
  `ChainComplex.LiftsAlongEpi` (read in
  `WeilConjectures.Algebra.Homology.ResolutionByClass`, lines 54–61) gives
  `∀ ⦃A B G : C⦄ (p : A ⟶ B) [Epi p] (g : G ⟶ B), T G → ...`,
  with `T G = IsConstructibleSheaf G`. A and B are unrestricted.
- Existence of E, e:E→G, h:E→A: the same definition concludes
  `∃ (E : C) (e : E ⟶ G) (h : E ⟶ A), S E ∧ Epi e ∧ h ≫ p = e ≫ g`.
- Flat and constructible E: `S E = ObjectProperty.flat E ∧ IsConstructibleSheaf E`.
  Read `CategoryTheory.ObjectProperty.flat` in
  `WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic`, lines 35–37:
  exactness of both `tensorLeft E` and `tensorRight E`. In this symmetric monoidal
  sheaf category the two tensor functors are naturally isomorphic by the braiding,
  so this is equivalent to the node's exactness of E⊗−, with no stronger condition.
- e is epi: `Epi e`, not merely an arbitrary map or sectionwise surjection.
- Required commutativity p∘h=g∘e: `h ≫ p = e ≫ g`, the same equality with Lean's
  diagrammatic composition convention.

Dependency declarations read and used:

- `def-weil-pbc-etale-site`: Mathlib match
  `AlgebraicGeometry.Scheme.smallEtaleTopology`, module
  `Mathlib.AlgebraicGeometry.Sites.Etale`, with `Scheme.Etale` in
  `Mathlib.AlgebraicGeometry.Morphisms.Etale` and
  `Scheme.ofArrows_mem_smallEtaleTopology_iff`. Their source signatures/docstrings
  identify étale X-schemes, finite limits, and jointly surjective covering families.
- `def-weil-pbc-etale-sheaves`: its mixed lean record explicitly permits the
  `CategoryTheory.Sheaf` / `ModuleCat` encoding for constructible material.
  The item's category is given explicitly in the node. This theorem does not need the
  record's additional set-valued local-constancy declarations. The recorded auxiliary
  module `WeilConjectures.AlgebraicGeometry.EtaleSheaves` is absent in both local source
  trees; this does not prevent the match: the required category is the existing generic
  `CategoryTheory.Sheaf` on the preceding site, not any auxiliary definition there.
- `def-constructible-constructible`: exact recorded
  `AlgebraicGeometry.Scheme.IsConstructibleSheaf` in
  `WeilConjectures.ConstructibleSheaf.Defs`, class at lines 321–323, with its full
  docstring at lines 277–320. This is the predicate named explicitly by the item.

Edge cases checked: the empty scheme is not excluded; the zero coefficient ring is
allowed (`CommRing`, not `Nontrivial`); zero G is allowed, with zero E a valid cover;
there are no restrictions on A or B beyond p being epi. No characteristic or invertibility
hypothesis occurs. There is no fixed nonempty stratification imposed. The shared universe
is exactly the source constructible-sheaf convention and does not restrict test schemes
using an independently smaller universe. No false-statement concern or correction found.

Searches (run through msearch.py; logs in this sandbox's searches.jsonl):

- LeanSearch: “Flat constructible sheaves lift morphisms along epimorphisms on the small
  etale site” — unavailable, Internal Server Error; no conclusion drawn from this service.
- LeanFinder: “flat constructible sheaves lift morphisms along epimorphisms on the small
  etale site” — eight hits about compatiblePreservingOfFlat, coherent-site epimorphisms,
  GeneratingSections, image sheaves and related generalities; none states this result.
- Loogle: `ChainComplex.LiftsAlongEpi, IsConstructibleSheaf` — zero hits,
  unknown identifier ChainComplex.LiftsAlongEpi.
- Mathlib grep: `LiftsAlongEpi|IsConstructibleSheaf|liftsAlongEpi_flat` — zero hits.
- Upstream rg for the item id and `liftsAlongEpi_flat_isConstructibleSheaf` — exact
  theorem at FlatModel.lean:119 and a use at line 205; no item-id annotation found.
- Project lean/Sheaf rg for those names — no hits.
- dag/lean_names_upstream.json rg for the name and FlatModel — no hits; the source
  declaration itself was opened and checked rather than relying on this index.

Validation: deliver2.py --no-push performs a real server-only scompile.py probe importing
this module and checking this declaration. The independent second reader supplies the
second-reading section and delivers; this worker does not push.

## Second reading by NP

I independently opened the item's node, the existing theorem and its ambient binders in
`WeilConjectures/SixFunctors/Etale/Derived/Finiteness/FlatModel.lean:43,105–140`,
the definition of `ChainComplex.LiftsAlongEpi` in `ResolutionByClass.lean:54–61`,
and all three statement-dependency node records. The source of this node is this Lean
source place itself; Stacks 095N is supporting literature, not the entire lifting theorem.
I also read `literature/stacks-project/etale-cohomology.tex`, lemma
`lemma-category-constructible-modules` (tag 095N): its hypotheses are a qcqs scheme and a
Noetherian coefficient ring, and it supplies finite affine generators and presentations.
These apply here because X is Noetherian and Λ is finite. No separatedness, characteristic,
or invertibility hypothesis is assumed throughout the source theorem.

Independent object/hypothesis/conclusion checklist, in the node's order:

1. Λ is a finite commutative ring: ambient `(Λ : Type (u + 1)) [CommRing Λ]`,
   and `[Finite Λ]` on the theorem. Exact; no domain, field, or nontriviality assumption.
2. X is a Noetherian scheme: ambient `{X : Scheme.{u}}` and `[IsNoetherian X]`.
   Exact; ambient Y is unused and is not a parameter of this theorem.
3. C is the category of Λ-module sheaves on the small étale site:
   `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)` in both properties.
   Exact. I read Mathlib `Scheme.Etale` (Morphisms/Etale.lean:158) and
   `smallEtaleTopology` / `ofArrows_mem_smallEtaleTopology_iff`
   (Sites/Etale.lean:51–65): étale X-schemes, X-morphisms, finite limits, and jointly
   surjective covering families. The mixed record of `def-weil-pbc-etale-sheaves`
   explicitly authorizes this ModuleCat encoding for constructible material. Its auxiliary
   set-valued predicates are not needed by this node; no dependency module is missing.
4. Constructibility is the source predicate, not a differently defined general sheaf
   predicate: `Scheme.IsConstructibleSheaf`, exactly the declaration recorded by
   `def-constructible-constructible`. Read its class and full docstring in
   `ConstructibleSheaf/Defs.lean:277–323`, and `IsFiniteSheaf` /
   `IsFiniteLocallyConstantSheaf` at lines 186–213. It existentially chooses
   `S : Scheme.Stratification X` with finite index `Fin S.n`, constructible locally closed
   strata and their immersions, and requires finite locally constant pullbacks on all
   strata. Finiteness means finitely generated geometric fibers for modules, as in the
   node. Exact; the general non-qc distinction discussed by the docstring causes no issue
   for Noetherian X and the node explicitly names this predicate.
5. Flatness means exactness of E tensor minus: `ObjectProperty.flat E`, read in
   `FromJoel/CategoryTheory/Abelian/Flat/Basic.lean:35–37`, asks for exactness of
   `tensorLeft E` and `tensorRight E`. I also read the `exactFunctor` accessors:
   preservation of finite limits and finite colimits. In this abelian symmetric monoidal
   sheaf category the braiding naturally identifies the two tensor functors, so the second
   condition is redundant, not an extra hypothesis. Exact.
6. Every epi p:A→B and every map g:G→B from constructible G: unfolding
   `ChainComplex.LiftsAlongEpi S T` gives
   `∀ ⦃A B G : C⦄ (p : A ⟶ B) [Epi p] (g : G ⟶ B), T G → ...`,
   with `T G = IsConstructibleSheaf G`. Exact order and scope; neither A nor B is
   required to be constructible or flat.
7. Existence of a sheaf E and maps e:E→G and h:E→A:
   `∃ (E : C) (e : E ⟶ G) (h : E ⟶ A), ...`. Exact, depending on p and g.
8. E is flat and constructible: `S E = ObjectProperty.flat E ∧ IsConstructibleSheaf E`.
   Exact; no requirement that E itself be globally free or constant.
9. e is an epimorphism: `Epi e`. Exact categorical epimorphism, with no sectionwise
   surjectivity or splitness assumption.
10. p composed with h equals g composed with e: `h ≫ p = e ≫ g`.
    Exact after translating diagrammatic composition.

Edge cases: empty X is allowed, including a zero-stratum stratification; zero Λ is allowed
because there is no `Nontrivial Λ`; zero G and arbitrary A,B are allowed. For zero G one
can take zero E and zero maps. There is no numerical n parameter to restrict, no nonempty
cover requirement, and no characteristic assumption. Universe u is arbitrary; Λ and module
carriers use the source's u+1 convention needed by this small étale site. No independent
smaller test universe or hidden extra instance is introduced.

Independent searches, using different wording from the first reader:

- LeanFinder via msearch: “Constructible module sheaf admits flat finite presentation
  lifting through a surjective sheaf morphism” returned eight finite-presentation and
  quasicoherent sheaf declarations, none this lifting statement.
- Loogle via msearch: `"liftsAlongEpi"` returned zero hits.
- LeanSearch via msearch: “A constructible sheaf on a noetherian scheme is covered by
  flat constructible sheaves compatible with lifting across an epimorphism” was
  unavailable (Internal Server Error); no negative mathematical conclusion drawn.
- Independent rg on Mathlib, upstream WeilConjectures, and project lean/Sheaf:
  `liftsAlongEpi|[Ff]lat.*constructible|constructible.*[Ff]lat`. Mathlib and lean/Sheaf
  have no matches; upstream identifies the exact theorem at FlatModel.lean:119 and its
  use at :205, together with the generic lifting infrastructure and related flat-model
  theorems. I opened the exact theorem rather than inferring a match from its name.

No mismatch found and no statement, dependency, signature, or declaration changed. There
are no new nodes or dependency modules to review and no statement_change or citer verdicts
requiring review. The existing source proof is reused; no proof was written in stage 2,
no hollow data were introduced, and no duplicate module was supplied. The node's proof
list is empty; the existing theorem's docstring nevertheless gives the finite affine
sections, finite étale lifting refinements, and finite direct sum of flat constructible
free sheaves step by step. Stage-2 new-module blueprint docstring conventions do not
require editing read-only upstream sources for an existing:true attachment.

Validation: the recorded lean.statement was independently compared byte for byte with the
source signature up to `:=`; all variables and universes are bound by the opened source.
The deliver2 dry run and final delivery run the existing-declaration import/#check probe
through scompile.py on the server (nice 19, two threads, 60 seconds per file). No delivered
Lean files exist, and no local compiler or library build is used.
