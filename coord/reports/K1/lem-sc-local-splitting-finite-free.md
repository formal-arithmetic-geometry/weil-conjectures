## Worker report

The module lean/Sheaf/AlgebraicGeometry/Modules/LocalSplittingFiniteFree.lean states
AlgebraicGeometry.Scheme.Modules.exists_openCover_split_shortExact, with one sorry proof.
No definitions, extra nodes, dependency modules or statement corrections are needed.

Hypothesis and conclusion correspondence:
- A scheme X: `{X : Scheme.{u}}`, using def-pc-scheme's recorded declaration.
- Three O_X-modules and their two composable maps: `S : ShortComplex X.Modules`.
  Its fields X₁, X₂, X₃, f and g give exactly the terms and maps, including g ∘ f = 0.
- Short exactness including both outside zeros: `hS : S.ShortExact`, which asserts
  exactness, monicity of f and epicity of g, not surjectivity on every open's sections.
- Constant finite ranks r_i: `(r₁ r₂ r₃ : ℕ)` and the three instances
  `[S.X₁.IsFiniteLocallyFreeOfRank r₁]`, `[S.X₂.IsFiniteLocallyFreeOfRank r₂]`,
  `[S.X₃.IsFiniteLocallyFreeOfRank r₃]`, using def-amb-finite-locally-free-module.
- An open cover: `∃ (ι : Type u) (U : ι → X.Opens), (⨆ a, U a) = ⊤ ∧ ...`.
  No fixed index set is prescribed; a point-indexed cover is in this universe.
- On every member: `∀ a, ∃ e : S.X₂.restrict (U a).ι ≅
  S.X₁.restrict (U a).ι ⊞ S.X₃.restrict (U a).ι, ...`.
- Isomorphism of sequences, not merely of middle objects: the two equations
  `(restrictFunctor (U a).ι).map S.f ≫ e.hom = biprod.inl` and
  `e.hom ≫ biprod.snd = (restrictFunctor (U a).ι).map S.g` identify the arrows
  with the split inclusion and projection, with identity identifications on the
  outer terms. Any isomorphism to the displayed split sequence can be adjusted
  by its outer automorphisms to have these identity identifications.

Dependency declarations read and used:
- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom,
  including the local-affine definition and morphism structure.
- WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree:
  SheafOfModules.IsFiniteLocallyFreeOfRank, defined by local free generators
  indexed by a type equivalent to Fin r.
- Mathlib.AlgebraicGeometry.Modules.Sheaf: Scheme.Modules.restrictFunctor and restrict.
- Mathlib.Algebra.Homology.ShortComplex.ShortExact: ShortComplex.ShortExact.
- Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts: biprod.inl and biprod.snd.
The recorded rank notion's scheme interpretation was also checked against
WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf,
IsFiniteLocallyFreeOfRank.exists_restrict_iso_free (lines 587–596).

Source read on the server (literature is not installed in this machine's clone):
literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-rr/
lem-sc-riemann-roch.md, lines 130–155. Its determinant paragraph says locally
that the sequence splits. The module docstring carries all three DAG proof steps:
local sections, inverse maps constructed using exactness, and coverage.

Edge cases checked before writing: zero ranks are allowed by ℕ and the biproduct
with a zero term; no positive-rank assumption or rank-additivity hypothesis is
added. For the empty scheme an empty cover is permitted, since its bottom open
is top. Nothing requires a nonempty scheme, affine scheme, field, Noetherian
hypothesis, or a particular characteristic. Exactness is sheaf exactness and does
not assert that sections on an arbitrary open form a short exact sequence.
All variables and the universe u are explicitly bound.

Searches for an existing statement (2026-10-11):
- msearch.py leansearch: "finite locally free sheaves short exact sequence locally split";
  service unavailable (Internal Server Error).
- msearch.py leanfinder: "short exact sequence of finite locally free sheaves splits
  locally on an open cover"; eight hits concerning finite generators and finite
  presentation, none a local splitting statement.
- msearch.py loogle: "ShortComplex.Splitting, SheafOfModules.IsFiniteLocallyFreeOfRank";
  zero hits; service reported unknown identifier ShortComplex.Splitting.
- msearch.py grep: "locally.*split|split.*locally" in Mathlib AlgebraicGeometry;
  zero hits.
- rg over WeilConjectures/AlgebraicGeometry, its module-sheaf extensions and
  lean/Sheaf/AlgebraicGeometry: local-freeness/descent and unrelated Koszul,
  field-extension and étale-cover splitting statements; no statement of this node.
- grep -rn "lem-sc-local-splitting-finite-free" over WeilConjectures: no hits.
- rg of exists_openCover_split_shortExact over Mathlib, WeilConjectures,
  lean/Sheaf and dag/lean_names_upstream.json: no existing name.
The landed DeterminantShortExact module cites this node as a proof dependency
but does not state it. Mathlib's projective-object global splitting statements
are not this open-cover assertion for locally free sheaves.

Validation: scompile.py K1 lem-sc-local-splitting-finite-free on the module:
exit 0, compiled in 2.5 seconds, no warnings. No node faults or disputed statements.

## Second reading by K1

Independent second reader, 2026-10-11. Read the sandbox node and complete Lean
module, both statement dependency nodes and their recorded declarations, and the
source blueprint on the server, lines 1–175 of lem-sc-riemann-roch.md. The source
place for this item is the blueprint determinant paragraph, not a Stacks lemma.
That paragraph states that a short exact sequence of finite locally free modules
splits locally. Although its application is to a proper smooth curve over an
algebraically closed field, the local splitting argument uses only the stated
scheme, exactness and finite local freeness; lifting finitely many quotient basis
sections near a point works on any scheme. No ambient curve hypothesis belongs
in this extracted generic lemma.

Object, hypothesis and conclusion checklist, in the order of the node:
1. Scheme X [def-pc-scheme]: `{X : Scheme.{u}}`. Read Mathlib Scheme.lean:42,
   including `local_affine`; it is the recorded general scheme, not an affine or
   field scheme. PASS.
2. Three O_X-modules E1, E2, E3: `S : ShortComplex X.Modules`, with terms
   `S.X₁`, `S.X₂`, `S.X₃`. Read `Scheme.Modules` in Mathlib Modules/Sheaf.lean:42:
   it is `SheafOfModules.{u} X.ringCatSheaf`, the Zariski structure-sheaf module
   category, with its canonical Abelian and (co)limit instances. PASS.
3. Arrows E1 → E2 → E3 and outside zeros, short exact:
   `S.f`, `S.g`, `S.zero` and `(hS : S.ShortExact)`. Read ShortComplex/Basic.lean:34
   and ShortExact.lean:35: exactness, Mono f and Epi g. These are precisely sheaf
   short exactness, not an extra assertion of sectionwise surjectivity. PASS.
4. Constant finite ranks r_i and local freeness of all three terms:
   `(r₁ r₂ r₃ : ℕ)` and `[S.Xᵢ.IsFiniteLocallyFreeOfRank rᵢ]` for i = 1,2,3.
   Read the dependency's recorded source class in LocallyFree.lean:133: free
   local-generators data with each generator index equivalent to `Fin r`.
   Read its scheme specialization `IsFiniteLocallyFreeOfRank.exists_restrict_iso_free`
   in WeilConjectures/Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:589, which gives
   exactly a Zariski cover with restrictions isomorphic to free modules of rank r.
   The predicate does not mean varying finite rank. No rank-additivity assumption
   or projectivity of a sheaf in the global sheaf category is introduced. PASS.
5. There exists an open cover of X: `∃ (ι : Type u) (U : ι → X.Opens),
   (⨆ a, U a) = ⊤ ∧ ...`. An arbitrary witnessing point-indexed cover fits Type u;
   this restricts no scheme or possible existence of a cover. PASS.
6. On every member the sequence is isomorphic to the displayed split sequence:
   `∀ a, ∃ e : S.X₂.restrict (U a).ι ≅
   S.X₁.restrict (U a).ι ⊞ S.X₃.restrict (U a).ι`. Read Mathlib's restriction
   functor and restrict abbreviation at Modules/Sheaf.lean:348–355: these are
   actual restrictions along an open immersion, using the canonical open
   inclusion, with no additional hypothesis to be supplied. PASS.
7. The two arrows become split inclusion and projection:
   `(restrictFunctor (U a).ι).map S.f ≫ e.hom = biprod.inl` and
   `e.hom ≫ biprod.snd = (restrictFunctor (U a).ι).map S.g`. These equations
   express the two squares, not merely an isomorphism of middle objects. Identity
   outer identifications do not strengthen the node: if a sequence isomorphism
   has outer automorphisms α, γ, composing its middle map with
   α⁻¹ ⊞ γ⁻¹ normalizes both outer maps to identities. Conversely this e and
   identity outer maps give the required sequence isomorphism. Outside zero maps
   commute automatically. The quantifiers choose a cover first, then an
   isomorphism separately on each member; no compatibility between different
   members is demanded. PASS.

Edge cases: all ranks can be zero; either outer term and the whole sequence can
be zero. No nonzero, positive-rank, nonempty, connectedness or characteristic
hypothesis occurs. For the empty scheme an empty index type is allowed and its
empty supremum is top; universal member conditions are vacuous. No empty cover
is permitted for a nonempty scheme, because bottom is then not top. The theorem
is polymorphic in explicitly declared u, with the module universe matching the
recorded scheme-module category; no independent too-small test universe is
introduced. No implicit unbound variable or universe remains.

Independent searches, using different terms from the first reading:
- msearch.py leansearch: "an extension of locally free O_X modules is locally
  isomorphic to the direct sum sequence". HTTP Internal Server Error; recorded
  unavailable, no search verdict inferred.
- msearch.py leanfinder: "vector bundle extensions split Zariski locally via a
  right inverse to the epimorphism". Eight hits: tilde sections, local generator
  data and topological vector bundle trivializations, none this statement.
- msearch.py loogle: `ShortComplex.ShortExact, "split"`. Zero hits; the service
  reports unknown identifier ShortComplex.ShortExact, so this is not positive
  evidence of absence.
- msearch.py grep: `rightInverse|split_shortExact|split.*[Ee]xact|[Ee]xact.*split`
  in Mathlib/AlgebraicGeometry. Two unrelated hits (projective spectrum and
  division-polynomial tactics), no local module-sheaf splitting.
- Independent rg over all WeilConjectures and repository lean/Sheaf for
  `split.*(locally|cover|restrict)|(?:locally|cover|restrict).*split` and the
  proposed declaration. Read the potentially relevant Adic/Extension.lean
  `IsAdicLisseSheaf.of_shortExact` and ConstructibleSheaf/KernelCokernel.lean
  `IsFiniteLocallyConstantSheaf.of_shortExact`: these concern adic/pro-étale or
  finite constant-coefficient étale sheaves and preservation of lisseness, not
  O_X-modules on Zariski opens. DeterminantShortExact cites this lemma but does
  not state it. No existing declaration matches the node.

H5–H9: no new definition or hollow data, no dependency module or new node, no
statement correction. The sole theorem has exactly a `sorry` proof. Both
module and theorem docstrings cite the correct source and blueprint id; the
proof docstring includes all three node steps (choose quotient sections via
lem-sc-local-section-quotient-finite-free; construct inverse splitting maps
using exactness and injectivity; the neighbourhoods cover). Imports, namespace,
line lengths and explicitly bound universes follow the contract. The node's
lean.statement is the file signature verbatim with whitespace normalized.

Mismatches found: none. No Lean or node content changed; appended this review
and recorded independent searches. Validation: scompile.py K1
lem-sc-local-splitting-finite-free on the delivered module returned exit 0,
compiled in 2.6 seconds, no warnings. The delivery dry run follows this review.
