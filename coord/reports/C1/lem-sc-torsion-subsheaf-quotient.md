## Worker report

Module: `Sheaf.AlgebraicGeometry.TorsionSubsheafQuotient`; declaration:
`AlgebraicGeometry.Scheme.Modules.torsion_subsheaf_quotient`. Its sole proof is `sorry`.
No definitions, new nodes, dependency replacements, or statement corrections are needed.

Clause-by-clause reading:

- An integral scheme is `(X : Scheme.{u}) [IsIntegral X]`; its generic point is
  `genericPoint X`. Mathlib's integral hypothesis includes nonemptiness, reducedness,
  and irreducibility; no curve, Noetherian, or finiteness hypothesis is imposed.
- A quasi-coherent O_X-module is `(F : X.Modules) [F.IsQuasicoherent]`.
- The torsion subsheaf is the existential object `T : X.Modules` with inclusion
  `i : T ⟶ F`, `Mono i`, and `T.IsQuasicoherent`. This states existence without creating
  a second definition or leaving data as sorry.
- Its sections are exactly those with zero generic germ: for every open U and section s,
  `∃ t : Γ(T, U), i.app U t = s` iff every proof hη of `genericPoint X ∈ U` gives
  `F.presheaf.germ U (genericPoint X) hη s = 0`. For a nonempty open the generic point
  belongs to U. For the empty open the right side is vacuous, and the left side holds
  because any sheaf of modules has a unique (zero) section on the empty open.
- At each x, membership in `Set.range (i.stalkLinearMap x)` is equivalent to
  `∃ a : X.presheaf.stalk x, a ≠ 0 ∧ a • s = 0`. Thus the stalk image is exactly the
  torsion submodule, with the meaning of torsion explicitly required by the node.
  Mono i already says T is a subobject; exactness of stalks makes the stalk map injective.
- The quotient F/T is the categorical `cokernel i`. Its torsion-free assertion is
  `∀ x s a, a ≠ 0 → a • s = 0 → s = 0`, on that cokernel's stalks, over O_{X,x}.
- The kernel assertion is the final existential vanishing equation h together with
  `Nonempty (IsLimit (KernelFork.ofι i h))`. This gives the full universal property,
  not merely that a composite vanishes. The map is `toSkyscraper LinearMap.id` from F
  to the skyscraper of F's generic stalk. The scalar annotation is `X.functionField`,
  definitionally O_{X,η}. The existing skyscraper is precisely the generic-point
  pushforward: its sections are `PLift (η ∈ U) → F_η` and its O_X-action is induced by
  germs. On Spec k(X), a module's associated sheaf has sections F_η on the sole nonempty
  open, so this is j_*F_η, with exactly the natural generic-germ map (no arbitrary map).

Dependency declarations and source signatures read:

- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`,
  `Mathlib.AlgebraicGeometry.Properties` (nonempty; section rings on nonempty opens domains).
- `pqf-def-coherent`: the recorded module `Sheaf.AlgebraicGeometry.Coherent` explains that
  quasi-coherence is the existing `SheafOfModules.IsQuasicoherent`, imported here from
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`. Its recorded
  `RingedSpace.IsCoherent` supplies the coherent clause of that dependency, which this
  item does not use. No duplicate quasi-coherence definition is introduced.
- `def-sc-function-field`: the recorded module `Sheaf.AlgebraicGeometry.FunctionField`
  defines the component product and explicitly reuses `AlgebraicGeometry.Scheme.functionField`
  for arbitrary integral schemes. This integral clause is used here via
  `Mathlib.AlgebraicGeometry.FunctionField`, where the abbrev is the generic stalk.
- `Scheme.Modules.Hom.stalkLinearMap`, `Scheme.Modules.skyscraper`, and
  `Scheme.Modules.toSkyscraper` from
  `WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk` supply the already defined
  stalk map and generic pushforward map. Their definitions and docstrings were read.
- Mathlib's sheaf-of-modules Abelian instance supplies cokernels; `KernelFork.ofι` and
  `IsLimit` express the kernel universal property.

Source check: the local Stacks checkout is absent on this machine, so opened the source at
https://stacks.math.columbia.edu/tag/0AXR and https://stacks.math.columbia.edu/tag/0AXT.
0AXR gives equivalence of torsion and zero generic germ; 0AXT gives the quasi-coherent
submodule and torsion-free quotient. The docstring carries all three DAG proof steps,
including pushforward quasi-coherence, stalk identification, and the local lifting argument.

Edge cases checked mathematically before writing: F=0; F=O_X (T=0); the closed-point
skyscraper on Spec Z (T=F, quotient zero); O_X plus that skyscraper (T the skyscraper);
X=Spec of a field (T=0 for every F); the empty open U; arbitrarily large quasi-coherent
modules. The empty scheme is excluded by the node's integral hypothesis itself, not by
an extra hypothesis. No characteristic constraint occurs. No disputed statement found.

Searches for an existing statement (all no matching sheaf theorem):

- `msearch.py ... leanfinder "torsion subsheaf of quasi coherent module integral scheme torsion free quotient"`:
  eight hits, including `Submodule.QuotientTorsion.torsion_eq_bot` and its domain
  torsion-free instance, and module tilde localization facts. These are algebraic facts,
  not this scheme theorem.
- `msearch.py ... loogle "Module.torsion, SheafOfModules"`: zero hits; unknown identifier
  Module.torsion (the algebraic notion is Submodule.torsion).
- `msearch.py ... grep "torsion.*(Quasicoherent|SheafOfModules)|Quasicoherent.*torsion" AlgebraicGeometry`:
  zero hits.
- `rg` of torsion, generic stalks, torsion subsheaf, and torsion submodule under
  `WeilConjectures/AlgebraicGeometry` and `lean/Sheaf/AlgebraicGeometry`: other torsion
  coefficient sheaves and generic-stalk lemmas, no exact statement.
- `rg` of the item id and proposed declaration name in `WeilConjectures`, `lean/Sheaf`,
  and `dag/lean_names_upstream.json`: no existing declaration.

Validation: `scompile.py C1 lem-sc-torsion-subsheaf-quotient` on the module completed
in 2.3 seconds, exit code zero, without warnings. Every variable and universe is explicit.

## Second reading by C1

Independent second reading of the node copy and the complete Lean module, with the three
statement-dependency nodes and their recorded source declarations open. No mathematical or
Lean mismatch found; the module and node signature are unchanged. The only delivery change
in this reading is this review report.

Source read independently: fetched the Stacks `divisors.tex` into the sandbox scratchpad
from https://raw.githubusercontent.com/stacks/stacks-project/master/divisors.tex and read
lines 1641–1725, including the section introduction, lemma-torsion-sections (0AXR),
definition-torsion, lemma-check-torsion-on-affines, and lemma-torsion (0AXT). Also checked
https://stacks.math.columbia.edu/tag/0AXR and https://stacks.math.columbia.edu/tag/0AXT.
The section has no standing Noetherian, curve, finite-type, or characteristic assumption.

Object/hypothesis/conclusion checklist, in the node's order:

- Integral scheme X: `(X : Scheme.{u}) [IsIntegral X]`. Read Mathlib Properties.lean:240:
  nonempty X and domain section rings on nonempty opens, equivalent to the node's integral
  scheme dependency. Correct; neither a curve nor an affine scheme is required.
- Generic point eta: `genericPoint X`, supplied by integral scheme irreducibility and
  scheme sobriety. This is the unique generic point of X, not a selected closed point.
  Correct; no additional point or genericity hypothesis.
- Quasi-coherent O_X-module F: `(F : X.Modules) [F.IsQuasicoherent]`. Read the dependency
  pqf-def-coherent and Coherent.lean: its quasi-coherence clause explicitly uses Mathlib
  `SheafOfModules.IsQuasicoherent` (Quasicoherent.lean:251), locally presented by free
  modules, equivalent on schemes to affine-local tilde modules. Its separate coherent
  predicate is irrelevant here. Correct; no coherence or finite presentation imposed.
- Submodule of F consisting of sections with zero generic germ:
  `∃ (T : X.Modules) (i : T ⟶ F), Mono i ∧ T.IsQuasicoherent ∧ ...` and, for every U,s,
  `(∃ t : Γ(T, U), i.app U t = s) ↔ ∀ hη : genericPoint X ∈ U,
  F.presheaf.germ U (genericPoint X) hη s = 0`. Mono is the categorical subobject
  inclusion; the section condition specifies its image exactly, and quasi-coherence
  specifies the required property. Correct. The order is X,F then one T,i working on
  every open and stalk, not separate choices depending on U or x.
- At each point the stalk is the torsion submodule of F_x over O_{X,x}:
  `∀ x s, s ∈ Set.range (i.stalkLinearMap x) ↔
  ∃ a : X.presheaf.stalk x, a ≠ 0 ∧ a • s = 0`. Read the upstream stalkLinearMap
  definition: it is the O_{X,x}-linear map induced by i. Stalk exactness makes the stalk
  of a monomorphism injective; using its image is exactly the embedded torsion submodule.
  Correct; nonzero annihilator is the node's explicit meaning over a domain.
- Quotient F/T is torsion-free: `cokernel i` is the sheaf-of-modules quotient, and
  `∀ x s a, a ≠ 0 → a • s = 0 → s = 0` uses its stalk and the same local ring.
  Correct; no merely global-section test or finiteness restriction.
- Equivalent kernel description for the natural map to j_*F_eta:
  the final `∃ h : i ≫ toSkyscraper (LinearMap.id : ... →ₗ[X.functionField] ...) = 0,
  Nonempty (IsLimit (KernelFork.ofι i h))` states the whole kernel universal property.
  Read FunctionField.lean:37: X.functionField is definitionally O_{X,eta}, matching
  def-sc-function-field's arbitrary integral-scheme clause; the component-product
  declaration is not mistakenly applied to general X. Read upstream SkyscraperSections,
  skyscraper, its scalar action, and toSkyscraper: sections are functions
  `PLift (eta ∈ U) → F_eta`, scalars act by germs, and the map sends s to its generic
  germ. These are precisely j_* of the module on the one-point Spec k(X), with the
  natural map specified in the node. Correct; the chosen map is not arbitrary.

Edge cases: the empty open has its unique zero section; the universal generic-germ
condition is vacuous there and image membership holds. Every nonempty open contains eta.
The empty scheme is excluded by the node's integral hypothesis itself. On Spec of any
field every module is torsion-free and T=0. F=0 gives T=0 and quotient zero; F=O_X gives
T=0; a closed-point quasi-coherent skyscraper on Spec Z gives T=F and quotient zero;
adding O_X gives exactly the skyscraper torsion part. Arbitrary characteristics and
infinite-rank modules are included. There is no index family or numerical n parameter.
The explicit universe u is arbitrary, shared with X.Modules and its stalks; it introduces
no extra smallness or test-object hypothesis. No unbound variable or universe occurs.

Independent searches using different phrases from the first reading:

- `msearch.py C1 lem-sc-torsion-subsheaf-quotient leanfinder
  "kernel of generic stalk map quasi coherent sheaf torsion quotient integral scheme"`:
  eight ideal-sheaf kernel results (Scheme.Hom.ker_apply and related declarations),
  concerning kernels of ring maps induced by scheme morphisms, not this module theorem.
- `msearch.py C1 lem-sc-torsion-subsheaf-quotient loogle "Submodule.torsion"`:
  twelve algebraic results, including the torsion submodule, its domain torsion-free
  quotient, and flat-module results; none constructs this quasi-coherent subsheaf.
  The inline annihilator formula is the node's explicit stalk condition, not a new
  definition duplicating Submodule.torsion.
- `msearch.py C1 lem-sc-torsion-subsheaf-quotient grep
  "torsionFree|IsTorsionFree|torsion_subsheaf|torsionSubsheaf" AlgebraicGeometry`: zero hits.
- Independent rg of torsion with subsheaf, generic, and quasi-coherence, and the exact
  declaration name, across Mathlib AlgebraicGeometry and ModuleCat/Sheaf, the full
  WeilConjectures source, project lean/Sheaf, and dag/lean_names_upstream.json: only
  coefficient n-torsion sheaves, generic torsion étale sheaves, and an algebra splitting
  comment. No duplicate notion or exact theorem. No new definition or dependency module
  is needed, and no statement_change exists to audit.

H5/H6/H8/H9: no new definitions, hollow data, or proved auxiliary theorems. The only
proof is the named theorem's `sorry`. Header, namespace, imports, and line widths meet
conventions. Both docstrings name 0AXR/0AXT and the blueprint id. The theorem docstring
faithfully follows all three node proof steps and their dependencies: kernel and
quasi-coherence, both directions of the stalk identification, and local lifting to prove
the quotient torsion-free. All four imports supply used notions or instances.

Validation: scompile.py with the absolute sandbox module path compiled on the server in
2.3 seconds, exit code 0, with no warnings. (An initial relative-path invocation from the
read-only repository could not locate the sandbox file; corrected to its absolute path.)
The node's lean.statement is verbatim the signature from `theorem` to before `:=`.
