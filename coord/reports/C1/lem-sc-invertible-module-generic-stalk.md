## Worker report

The module `Sheaf.AlgebraicGeometry.InvertibleModuleGenericStalk` states all three clauses
in `AlgebraicGeometry.Scheme.Modules.invertible_module_generic_stalk`, with one `sorry`.
It defines no new notion and makes no statement correction.

Hypotheses and objects, clause by clause:

- `X : Scheme.{u}` and `[IsIntegral X]` give exactly an arbitrary integral scheme; no
  curve, finite type, Noetherian, or base-field restriction is imposed.
- `L : X.Modules` and `[L.IsInvertible]` are the recorded invertible O_X-module notion.
- `η := genericPoint X` chooses the unique generic point; `X.functionField` is precisely
  the structure-sheaf stalk there, equipped with Mathlib's field instance.
- The explicit carrier `↑(TopCat.Presheaf.stalk L.val.presheaf x)` (abbreviated S x
  in this report only) is the actual module stalk, with the module structure
  over `X.presheaf.stalk x` supplied by `PresheafOfModules`.
- `lam x` is `TopCat.Presheaf.stalkSpecializes` for the specialization of η to x.
  Its definition is the colimit map sending a germ at x to the same section's germ at η;
  `germ_stalkSpecializes` states this compatibility. Thus no arbitrary maps are hypothesized.
- `ρ x := algebraMap (X.presheaf.stalk x) X.functionField` is the canonical germ map:
  Mathlib's `stalkFunctionFieldAlgebra` defines it using structure-sheaf specialization.
  Its injectivity follows from Mathlib's `IsFractionRing` stalk instance.
- Clause 1: `∀ x, Nonempty (Module.Basis PUnit ... (S x))` expresses freeness of rank one
  by existence of a singleton basis; `Module.rank X.functionField (S η) = 1` explicitly
  states dimension one at η, without needing a finite-dimensional hypothesis.
- Clause 2: `Function.Injective (lam x)` gives injectivity at every x. The generator
  condition is exactly `Submodule.span (X.presheaf.stalk x) {e} = ⊤`. For every such e,
  the existential singleton basis `b` with `b PUnit.unit = lam x e` says its generic
  image is a basis. The range equality with `{τ | ∃ a, τ = ρ x a • lam x e}` is exactly
  O_{X,x} times that basis vector, via the specified embedding into the function field.
- Clause 3: `∀ U : X.Opens, ∀ hU : Nonempty U` quantifies over every nonempty open.
  Generic-point membership `hη` is obtained from `genericPoint_spec` and nonemptiness.
  `lamU := L.val.presheaf.germ U η hη` is the map specified in the node.
  Its injectivity and the equality of its range with
  `{τ | ∀ x, x ∈ U → τ ∈ Set.range (lam x)}` give both requested assertions.

Dependency declarations read and used:

- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral` (nonempty and integral section rings).
- `def-sc-function-field`: `Sheaf.AlgebraicGeometry.FunctionField`,
  `AlgebraicGeometry.Scheme.functionFieldOfComponents` was read. Its docstring and record
  expressly delegate this node's arbitrary integral-scheme case to
  `Mathlib.AlgebraicGeometry.FunctionField`, `AlgebraicGeometry.Scheme.functionField`.
  The component-product definition is not applicable to this integral-scheme statement;
  its designated Mathlib specialization is used directly, without a duplicate definition
  or an unused import of the component-product module.
- `def-sc-invertible-module`: `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` (local structure-sheaf trivializations).
- `def-weil-pbc-module-stalk`: the mathlib_match declarations
  `TopCat.Presheaf.stalk` and `PresheafOfModules.germ_ringCat_smul`, with the actual
  commutative-ring stalk module instance in `Mathlib.Algebra.Category.ModuleCat.Stalk`.

Sources: the local Stacks checkout is absent. Read the stated places directly at
https://stacks.math.columbia.edu/tag/01X5 (part 2, constant meromorphic-section sheaf)
and https://stacks.math.columbia.edu/tag/02OZ (proof of case 1, generic dimension one).
The theorem docstring carries all nine steps of the node's natural-language proof,
including the structure-sheaf intersection lemma and gluing.

Edge cases checked: an integral scheme is nonempty by definition, so the empty scheme
is correctly excluded by the node's own hypothesis. The empty open is excluded only in
clause 3. No quasi-compactness of U or finiteness of its cover is imposed. Arbitrary
characteristic and dimension are allowed, including a single field spectrum. A zero
module cannot be invertible on a nonempty scheme. The generator condition never treats
zero as a generator of a nonzero rank-one stalk. The basis index PUnit has exactly one
point; the arbitrary universe u permits schemes and modules in every universe.

Searches (recorded also in searches.jsonl):

- LeanFinder: "An invertible module on an integral scheme embeds in its generic stalk":
  eight hits about ModuleCat.Tilde localization, no statement of this theorem.
- Loogle: "TopCat.Presheaf.stalkSpecializes, Module.Basis": zero hits.
- msearch grep: "stalkSpecial|stalk.*[Gg]eneric|generic.*[Ss]talk", AlgebraicGeometry:
  25 hits, chiefly structure-sheaf specialization and function-field results, no match.
- LeanSearch: "invertible module stalk generic point integral scheme": unavailable
  (service Internal Server Error); no negative verdict inferred from this failure.
- rg in Mathlib's Stalks.lean located stalkSpecializes and germ_stalkSpecializes; their
  full signatures and definitions were read, and supply the maps needed here.
- rg "generic.*stalk|stalk.*generic|invertible_module_generic_stalk" in lean/Sheaf,
  WeilConjectures, and dag/lean_names_upstream.json: rational-function identifications,
  unrelated étale generic-stalk results, and a citation of this lemma in the Cartier
  section theorem; no existing declaration of this statement or collision for its name.
- grep for the item id in WeilConjectures: no occurrence.

No node fault or STATEMENT-DISPUTED issue was found. All variables and the universe are
explicitly bound. The only postponed proof is the named theorem above.

## Second reading by C1

Independent reading of the sandbox node and Lean module, the four statement-dependency
nodes, and their actual declarations. Verdict: the statement is exactly the node's
statement; no Lean or node repair was needed. Only this review section was appended.

Source check: read the actual Stacks `divisors.tex` from
https://raw.githubusercontent.com/stacks/stacks-project/master/divisors.tex,
labels `lemma-meromorphic-functions-integral-scheme` (01X5) and
`lemma-regular-meromorphic-section-exists` (02OZ), and their proofs; also checked
https://stacks.math.columbia.edu/tag/01X5 and
https://stacks.math.columbia.edu/tag/02OZ. The local checkout is absent.
01X5 assumes an arbitrary integral scheme and quasi-coherence; local triviality of an
invertible module supplies quasi-coherence. 02OZ case (1) assumes integrality alone and
uses generic dimension one. Its alternative cases' finiteness and Noetherian conditions
are not hypotheses of case (1). The intersection assertion is the node's explicit
invertible-case argument, not a literal extra clause asserted by 01X5. The nine proof
steps in the node correctly derive it by local trivialization and sheaf gluing.

Node inventory and matching Lean, object by object and clause by clause:

1. Object X, an arbitrary integral scheme: `(X : Scheme.{u}) [IsIntegral X]`.
   PASS. Read `AlgebraicGeometry.IsIntegral` in Mathlib Properties: nonempty X and
   domain section rings on every nonempty open. This is equivalent to the dependency
   node's nonempty reduced irreducible scheme definition. No curve, base field,
   separatedness, dimension, Noetherian, finite type, or quasi-compactness assumption.
2. Object eta, its generic point: `let η := genericPoint X`. PASS. Integrality gives
   irreducibility and scheme sobriety supplies the canonical generic point; its
   uniqueness makes choosing this point equivalent to the node's eta.
3. Object k(X) = O_{X,eta}, a field: `X.functionField`. PASS. Opened Mathlib
   FunctionField: it abbreviates `X.presheaf.stalk (genericPoint X)` and its field
   instance assumes exactly `[IsIntegral X]`. Opened the dependency node
   `def-sc-function-field` and Sheaf FunctionField: their explicit arbitrary integral
   scheme clause designates this same Mathlib declaration. The component product is
   the separate nonintegral-curve clause, so importing or instantiating that product
   here would give a different carrier. No dependency repair or private definition.
4. Object L, an invertible O_X-module: `(L : X.Modules) [L.IsInvertible]`. PASS.
   Opened Mathlib Modules.Sheaf: `Scheme.Modules` is `SheafOfModules.{u}` over
   `X.ringCatSheaf`. Opened upstream Modules.Invertible: its `IsInvertible` gives a
   neighborhood of every point with a structure-sheaf trivialization. On an open
   immersion its restriction pullback is restriction to that open. This is exactly
   locally free of rank one, hence quasi-coherent, not tensor invertibility of a
   different category. The node's dual definition is not used by this item.
5. Object L_x with its O_{X,x}-action: the carrier
   `↑(TopCat.Presheaf.stalk L.val.presheaf x)` and scalar ring `X.presheaf.stalk x`.
   PASS. Read both the RingCat and CommRingCat stalk module instances in Mathlib
   ModuleCat.Stalk and `germ_smul`: the latter uses preservation of filtered colimits
   by forgetting commutative rings. It supplies the actual commutative stalk action,
   not a fresh action or a stalk of the structure sheaf substituted for L.
6. Maps lambda_x, sending sigma_x to sigma_eta:
   `lam x := TopCat.Presheaf.stalkSpecializes L.val.presheaf
   ((genericPoint_spec X).specializes (Set.mem_univ x))`. PASS. Opened the colimit
   definition in Mathlib Topology.Sheaves.Stalks: for eta specializing to x it goes
   from the stalk at x to the stalk at eta, in precisely the required direction.
   `germ_stalkSpecializes` identifies the composite with the germ at eta.
   These maps are defined canonically, not extra arbitrary-map hypotheses.
7. Embedding rho_x of O_{X,x} into k(X):
   `ρ x := algebraMap (X.presheaf.stalk x) X.functionField`. PASS. Read
   `stalkFunctionFieldAlgebra`: its map is structure-sheaf `stalkSpecializes` for
   the same specialization. The subsequent `IsFractionRing` instance for every
   stalk gives injectivity. Thus injectivity is already supplied by the existing
   library and does not need an additional hypothesis or conclusion here.
8. Clause 1, every stalk free of rank one:
   `∀ x, Nonempty (Module.Basis PUnit.{u + 1} (X.presheaf.stalk x) ...)`.
   PASS: existence of a basis indexed by a singleton is exactly free rank one over
   the domain stalk ring. Generic dimension one is separately stated by
   `Module.rank X.functionField ... = 1`; over a field rank is vector-space
   dimension, so this adds no finite-dimensional assumption.
9. Clause 2, injectivity for every point: `∀ x, Function.Injective (lam x) ∧ ...`.
   PASS: applies independently of whether a generator has been chosen.
10. Clause 2, every generator: `∀ e, Submodule.span (X.presheaf.stalk x) {e} = ⊤ → ...`.
    PASS: spanning by the singleton is exactly the node's generating element.
    Its generic image is a basis via `∃ b : Module.Basis PUnit ...,
    b PUnit.unit = lam x e`. This existential singleton basis says exactly that
    the specified vector is a basis, not just that some unrelated basis exists.
11. Clause 2, image formula for that same e:
    `Set.range (lam x) = {τ | ∃ a : X.presheaf.stalk x, τ = ρ x a • lam x e}`.
    PASS: scalars come from the whole local ring via the specified embedding, and
    the basis and image assertions have the same universally quantified e.
12. Object U and lambda_U, for each nonempty open:
    `∀ (U : X.Opens) (hU : Nonempty U), ...` and
    `lamU := TopCat.Presheaf.germ L.val.presheaf U η hη`. PASS: `hη` comes from a
    chosen point of U and specialization of eta; no extra membership assumption.
    All membership proofs are propositionally irrelevant, so the choice has no
    effect on the map. Its source is the module of sections L(U).
13. Clause 3, section injectivity and exactly the intersection of stalk images:
    `Function.Injective lamU ∧ Set.range lamU = {τ | ∀ x : X,
    x ∈ U → τ ∈ Set.range (lam x)}`. PASS. This quantifies over every point of U,
    not just closed or affine points, with no chosen cover or finite-intersection
    restriction. The quantifier order agrees with the node throughout.

Edge cases: an empty scheme is excluded by integrality itself; a zero module on an
integral (therefore nonempty) scheme is excluded by local rank-one triviality. The
empty open is excluded only where the node excludes it, in clause 3. There is no
empty index-set hypothesis: PUnit is the fixed one-element basis index. No parameter
n or characteristic restriction occurs. A field spectrum, higher-dimensional and
non-Noetherian integral schemes, and non-quasi-compact opens are all covered. The
universe u is explicitly declared and arbitrary; Modules and stalks use their actual
universe-u carriers. Choosing PUnit in u+1 changes only the singleton index universe,
not the class of modules or schemes. All term variables are explicitly bound.

Independent searches, using different phrasing from the first reader:

- LeanFinder via msearch: "A line bundle over an integral scheme has rational sections
  identified with its rank one generic fiber, and regular sections are the intersection
  of local lattices". Eight hits: affine Tilde sections and structure-sheaf local
  fractions, not this general invertible-module statement.
- Loogle via msearch: `"IsInvertible", "germ"`. Zero hits.
- LeanSearch via msearch: "Regular sections of a locally free rank one sheaf inject
  into its generic fiber on an integral scheme". Service Internal Server Error;
  unavailable, with no negative verdict inferred.
- Direct rg for `line.?bundle`, rational sections, and invertibility paired with
  stalk/generic/germ in Mathlib AlgebraicGeometry, upstream WeilConjectures and
  project lean/Sheaf. Affine Tilde and structure-sheaf results do not state all
  clauses for arbitrary invertible modules. Upstream Curve.Picard explicitly says
  rational sections of line bundles are not available; Curve.RiemannRoch's divisor
  realization has smooth proper curve hypotheses and a different conclusion.
  Project NonzeroSectionIntegralCartier only cites this lemma in its proof.
- Direct rg for the theorem name and blueprint id in the upstream source, the project
  modules and dag/lean_names_upstream.json found no existing declaration or collision.

H4/H5/H6/H8/H9: no new definition nodes, dependency modules, or statement correction
are present or needed. The theorem is the module's only declaration, with its sole
proof `by sorry`; all let-bound objects use existing definitions, without hollow data.
The module and theorem docstrings name both source places and the blueprint id.
Compared the theorem's numbered proof paragraphs against all nine node proof steps:
trivializations; well-defined semilinear specialization; compatible stalk isomorphisms;
rank one; stalk injectivity and generator formula; section injectivity; inclusion in
intersection; local preimages; gluing. All are represented in order. Lines are at most
100 characters and declaration namespace is the upstream AlgebraicGeometry namespace.

Validation: compiled the unchanged module with scompile.py on the server: exit code 0,
Compiled in 1.9 s, no warnings or errors. A direct textual extraction confirmed that
`lean.statement` is verbatim the signature in the module. No mathematical mismatch,
node fault, missing dependency, or STATEMENT-DISPUTED issue was found.
