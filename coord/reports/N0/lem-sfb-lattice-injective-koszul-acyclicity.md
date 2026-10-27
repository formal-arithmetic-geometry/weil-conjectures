## Worker report

The module `Sheaf.CategoryTheory.LatticeInjectiveKoszulAcyclicity` states
`Profinite.LatticeInjectiveKoszul.acyclicity`, with one postponed theorem and real
constructions of its fixed sheaf Hom. The node is unchanged except for `lean`.
No statement correction, disputed statement, new node or dependency repair is needed.

Hypotheses and clauses, read against the node:

- A commutative condensed ring is `(R : Profinite.CondensedRing.{u})
  [IsCommMonObj R.X]`; `Modules R` is the existing internal module category,
  `Mod (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u+1}) R.X`.
  The universe `u` is explicit. Profinite objects have universe `u+1` and
  morphisms universe `u`; no equality of these levels is imposed.
- Rank is unrestricted `(r : ℕ)`, including zero. `Equivariant R r` is the
  existing `Action (Modules R) (Multiplicative (Fin r → ℤ))`, equivalent to
  the specified one-object lattice diagram category by
  `Action.functorCategoryEquivalence`.
- The cubical terms, translations and incoming boundaries are the recorded
  `LatticeCubical.term R r a (𝟙_ (Modules R))`, `translation` and `incoming`.
  The tensor unit is the existing regular module, so this is L_a(R).
- `∃ K : KoszulModel R r` asserts existence of the functor, rather than
  assuming a model. Its `coordinates` are exactly the finite biproducts
  indexed by a-element subsets, including empty index types outside [0,r].
  Its `differential` uses the existing `differentialEntry`: the sum over
  i in J, sign (-1)^(number of j<i), and operator T_i-1. Its `maps` are
  coordinatewise maps. This existing specification determines K up to the
  stated coordinates; no arbitrary complex or stronger input is substituted.
- `K.functor.Additive` and exactness of its composite with every
  `HomologicalComplex.eval ... a` render additivity and degreewise exactness.
- `K.augmentation` is natural from the actual limit invariants concentrated
  in degree zero. `KoszulModel.augmentation_zero` specifies the true invariant
  inclusion on each degree-zero coordinate. No extra hypothesis is supplied.
- `rawHom` uses the recorded `SheafOfModules.homObj`, with endpoints read
  through the fixed internal/section-module equivalence. Conjugation is
  precomposition by translation by -v followed by postcomposition by T^v.
  `conjugationDifference` maps to the product over ALL v of these maps minus
  identity, and `fixedHom` is its kernel. Thus this is precisely the submodule
  fixed by all conjugations, rather than global equivariant morphisms only.
- H is a functor of genuine cochain complexes. Its coordinates c identify its
  terms with `fixedHom`. The differential equation after the kernel inclusion
  specifies precomposition with the cubical incoming boundary. The equation
  for `H.map f` specifies postcomposition with f, so its coefficients and maps
  are exactly the internal equivariant Hom complex.
- e is a NATURAL ISOMORPHISM OF COCHAIN COMPLEXES to the section-module image
  of K. This retains the node's stronger actual-complex identification, not
  just an isomorphism of cohomology groups. It also induces the corresponding
  isomorphism in the derived category.
- A is a natural augmentation into H. Its equality after e is precisely the
  image of K's invariant augmentation under the canonical single/map-complex
  comparison. Hence e includes the augmentations. A is forced by this equality
  and the invertible e; it is not an unspecified replacement augmentation.
- For every P, integral degree a, profinite U, local section x, lattice vector v
  and subset I, the inverse formula evaluates e.inv on `[v,I](1)` and equals
  T^v applied to the I-coordinate of x. `generatorSection` is the existing
  coproduct injection applied to the actual section-ring unit. Taking v=0
  gives evaluation on origin generators; conversely equivariance forces the
  stated inverse everywhere. Evaluation uses the local map at `Over.mk (𝟙 U)`
  directly: `PresheafOfModules.homObjEvalId` is specialized to equal object,
  morphism and coefficient universes and cannot be used on this site.
- For every J with `[Injective J]` IN THE ACTION CATEGORY and every profinite
  U, the theorem asserts injectivity of the first augmentation map, exactness
  at degree zero, and `Function.Exact` at every positive integral degree.
  This includes the top surjection because degree r+1 is the empty biproduct.
  It finally asserts `QuasiIso (K.augmentation.app J)` itself.

Dependency declarations inspected and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, its full
  abbreviation and docstring, through the cubical module.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `ModObj`,
  `Mod.Hom`, `Mod.regular`; the recorded generic module-object definition.
- `def-weil-size-convention` has a convention record, with no declaration.
- `Sheaf.CategoryTheory.LatticeCubicalSheafResolution`: `term`, `translation`,
  `incoming`, `categorical`, `tensorComparison`, `resolution`; read the entire
  module, including the augmented contraction and coefficient naturality.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj`, `homObjMap`; their full local-site signatures and
  docstrings. The underlying local maps are those of
  `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom`.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `Injective`, read
  its extension-across-monomorphisms signature (lines 32–34).
- `Sheaf.CategoryTheory.DiscreteLatticeKoszulResolution`: existing
  `Modules`, `Group`, `Equivariant`, `invariants`, `Subsets`, `generator`,
  `differentialEntry`, `KoszulModel`. Read their complete definitions and
  docstrings (lines 45–164). Reused rather than duplicating the signed complex.
- Proof imports retained: `SheafOfModules.tensorClosed` in the upstream
  TensorClosed module (definition and naturality signature read);
  `PresheafOfModules.freeYonedaEquiv` (Generator, lines 53–70);
  `PresheafOfModules.sheafification` and `sheafificationAdjunction`
  (Sheafification, lines 47–62 and 125 onward). The section equivalence
  `InternalAbelianSheafModule.sectionModuleEquivalence` is already public
  through the cubical dependency. DerivedCategory/QuasiIso is also public
  through the existing complex API.

The downstream discrete-lattice theorem's module already owns `KoszulModel`.
Importing it is necessary to avoid a second definition of the same notion.
The maintainer must omit the reverse proof import from that module to this one,
which would close the import cycle. This delivery does not modify that module
or its node, and does not add a cyclic DAG dependency. Its existing theorem is
not used as a proof or an assumption here.

Edge cases checked mathematically before writing and during rereading:
rank zero has only the empty subset and trivial lattice, giving identity
augmentation and no positive terms; rank one gives T-1; rank two gives the
opposite deletion signs. Negative degrees and degrees above r have empty subset
index. The top exactness clause says surjectivity onto the last term. Zero
module and zero coefficient ring give zero maps and trivial exact sequences.
The empty profinite object is included in the unrestricted U quantifier.
No section functor is assumed exact and no free test module is assumed projective.

Sources read: `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3),
and Stacks `sites-modules.tex`, `lemma-j-shriek-flat` (Tag 03EV) and
`equation-map-lower-shriek-OU-into-module`. The latest blueprint delegates the
boundary calculation to the open-coefficient input; the accepted six-step node
contains the algebraic refinement. The theorem docstring reproduces all six
proof steps and their cited dependencies.

Searches actually run via the prescribed msearch wrapper:

- leanfinder: “For an injective lattice action on condensed modules the finite
  signed Koszul complex is exact on sections and its invariant augmentation is
  a quasi-isomorphism”: eight hits, including standard representation resolution
  and general injective-complex lemmas; none states this theorem.
- loogle: `CategoryTheory.Injective, CochainComplex`: twelve hits on injective
  complexes/resolutions, no lattice/sheaf Koszul statement.
- leansearch: “Koszul complex of commuting automorphisms on sheaves injective
  invariant augmentation exact sections”: eight hits, including
  `ShortComplex.Exact.descToInjective`, but no exact statement.
- grep: `Koszul|koszul`: three Mathlib hits (connections, local-cohomology TODO,
  regular-sequence TODO), no matching construction or theorem.
- rg on `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for lattice/Koszul and exact helper names: found the existing `KoszulModel`
  and several later derived comparisons; no exact theorem. Search by item id
  in `lean/WeilConjectures` found no match. Searched all source trees for
  `LatticeInjectiveKoszul|conjugationDifference|generatorSection`: no full-name
  clash (an unrelated private generatorSection exists under AlgebraicGeometry).

Validation: scompile.py compiled the final file both as sandbox and final library
module without errors or warnings, approximately nine seconds each. All definitions
have real data; `acyclicity` alone has proof `sorry`.

## Second reading by N0

The delivered section with this heading was the worker re-reading its own work ("an
in-session second reading by the same dispatched worker; no independent worker was
started"). The maintainer's reviewer replaced it with the independent clause-by-clause
reading below (review of 582fa9683ee9, 2026-10-24). The Lean and the node record are unchanged.

Node clauses, the Lean that renders each, and the verdict:

1. R is a commutative condensed ring, and M_R is its internal module category:
   `(R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]`, and `Modules R` = `CondensedAction.Modules R`
   = `Mod` over `R.X` in `Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u+1}`.
   These are the recorded sk-def-sfb-condensed-ring and sk-def-sfb-module-objects (`CategoryTheory.Mod`). Exact.
2. r ≥ 0, D = Z^r, and E_R = Fun(BD, M_R): `(r : ℕ)` is unrestricted, and
   `Equivariant R r = Action (Modules R) (Multiplicative (Fin r → ℤ))`. This is equivalent to the
   one-object functor category by Mathlib's `Action.functorCategoryEquivalence`. Exact.
3. Small coherent profinite site: the same `coherentTopology Profinite.{u}` convention as the
   recorded dependencies (objects in u+1, morphisms in u). No universe equality is imposed. Exact.
4. L_•(R) is the cubical complex of lem-sfb-lattice-cubical-sheaf-resolution:
   `LatticeCubical.term R r a (𝟙_ (Modules R))` = ∐ over D × Directions r a of the unit. Translation is
   `translation`, and the boundary ∂_{a+1} : L_{a+1} → L_a is `incoming`. All are recorded declarations of that stmt_dep. Exact.
5. K(P)^a = ⊕_{|I|=a} P with (dx)_J = Σ_{i∈J} (−1)^{#{j∈J : j<i}} (T_i − 1) x_{J∖i}, in degrees 0..r and zero
   elsewhere: `∃ K : KoszulModel R r`. Its `coordinates` are biproducts over `Subsets r a`,
   which is empty outside [0,r]. Its `differential` is `differentialEntry`, which uses the same
   sign and the operator `ρ(generator i) − 1`. Its `maps` act diagonally. Every model
   is determined up to a canonical isomorphism, so the ∃ form also asserts that K exists. Exact.
6. K is additive and each degree functor is exact: `K.functor.Additive` and
   `exactFunctor _ _ (K.functor ⋙ eval a)` for all a. Exact.
7. The natural augmentation e_P : P^D[0] → K(P) given by the invariant inclusion: `K.augmentation`. Its
   source is `invariants ⋙ single 0`, and `augmentation_zero` makes it the limit inclusion. Exact.
8. Hom_{E_R}(L_a(R), P) is the conjugation-fixed part of the internal Hom of def-pur-sheaf-hom:
   `rawHom` = `SheafOfModules.homObj` (the recorded declaration), read through the
   section-module equivalence. `conjugationDifference` = Pi.lift over all v of
   `homObjMap (τ_{−v}) (T^v) − 𝟙`, and `fixedHom` is its kernel. homObjMap precomposes with
   its first argument, so a section f is fixed exactly when f∘τ_v = T^v∘f for every v, i.e. when it is
   equivariant. Exact.
9. Evaluation on [0,I] gives a natural isomorphism of cochain complexes, with the inverse
   [v,I] ↦ T^v x_I: H is a functor to cochain complexes of section modules, and
   c : H.X a ≅ fixedHom. Its differential is precomposition with `incoming`, with no extra sign, and
   H.map f is postcomposition with f. Both are stated after `kernel.ι`, which is mono. The natural
   isomorphism e : H ≅ K ⋙ (section equivalence).mapHomologicalComplex is a chain isomorphism. The inverse formula
   holds for every U, every section x, every v and every I, at `Over.mk (𝟙 U)` on `generatorSection v I U` = ι_{(v,I)}(1).
   A map from a coproduct of copies of the unit, restricted to Over U, is determined by these values.
   So `e.inv ≫ c.hom ≫ ι` is completely pinned, and c and H are not free data.
   Exact.
10. "Including their augmentations": A ≫ e.hom = (singleMapHomologicalComplex).inv ≫ map(e_P).
   This determines A from e. Since e.inv is pinned by item 9, A's value on [v,∅](1) is the
   invariant section itself, which is ε^* of the map R → P, 1 ↦ x. So the
   Hom-side augmentation is fixed, but only through this computation, not as an
   explicit ε^* clause on the Hom object from R. Accepted. Advisory: it is not a missing hypothesis or object.
11. For J injective in E_R (Mathlib `Injective`, the def-sp-injective-resolutions record), the theorem asserts the following.
   On U-sections for every `U : Profinite.{u}`, J^D → K(J)^0 is injective. The augmented sequence is exact at K(J)^0
   and at every positive degree. At a = r the next term is the empty biproduct, which gives the final surjection.
   `QuasiIso (K.augmentation.app J)` is asserted separately. Exact.

Edge cases: r = 0 (only ∅, the trivial lattice), a < 0 and a > r (empty index sets), the empty
profinite set (U is unrestricted), and the zero module and zero ring are all covered with no extra
hypothesis. No section functor is assumed exact, and no test module is assumed projective.

Searches: in Mathlib and the side-live `lean/Sheaf` tree, `KoszulModel`, `homObj`,
`conjugation`, and `LatticeInjectiveKoszul|fixedHom|generatorSection` found no existing
statement and no name clash. LatticeKoszulInjectiveNormalization is a complex-level derived
normalization that takes the model as input, not a duplicate.

Mismatches: none in substance. Maintainer advisory: `KoszulModel`, `Equivariant`, `invariants`
and `differentialEntry` are plain definitions in the module of the theorem
lem-sfb-discrete-lattice-koszul-resolution. That node's proof_deps cite this item. The worker
listed the reverse proof import as left out (stages/2 §3 rule 7). Before stage 3, move these
definitions into an existing:true definition-node module.
