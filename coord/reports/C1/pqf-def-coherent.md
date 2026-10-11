## Worker report

The module `Sheaf.AlgebraicGeometry.Coherent` defines the three notions in the
node: `AlgebraicGeometry.Scheme.Modules.IsQuasicoherent`,
`IsFiniteType`, and `IsCoherent`. It uses Mathlib's `Scheme`, `Scheme.Opens`,
`IsAffineOpen`, `Scheme.Modules.restrict`, `AlgebraicGeometry.tilde`,
`SheafOfModules.free`, categorical `Epi`, and `kernel`.

For quasi-coherence, the Lean binders are `x : X`, an open `U : X.Opens`, an
affineness witness, a ring `R`, and an isomorphism
`e : Spec R ≅ U.toScheme`; the clause `x ∈ U` and an `R`-module `M` with
`F.restrict (e.hom ≫ U.ι) ≅ AlgebraicGeometry.tilde M` render the affine-local
tilde condition. The explicit affine isomorphism makes the phrase
“Spec A = U” precise while allowing the chosen open to be represented in the
scheme category.

For finite type, `∀ x, ∃ U n, x ∈ U ∧ ∃ f, Epi f` renders a local surjection
from a finite free module. The finite free object is
`SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin n))`;
`ULift` is required only to place the finite index type in the scheme's universe.
For coherence, `IsCoherent X F` is the conjunction of this finite-type clause
and `∀ U n f, ∃ m g, Epi g`, where `g` is from a finite free module onto
`kernel f`, rendering the kernel clause for every open and every finite-free map.

The dependency `def-pc-scheme` is represented by Mathlib's
`AlgebraicGeometry.Scheme`; `def-weil-sheaf-of-modules-category` is represented
by Mathlib's `SheafOfModules` and the scheme specialization `Scheme.Modules`.
No project declaration was duplicated.

Edge cases checked: `n = 0` and `m = 0` are allowed (`Fin 0`), arbitrary open
subschemes including the empty open are quantified, and the quasi-coherent
clause quantifies every point. The universe lift avoids excluding schemes at a
nonzero universe.

Searches: the node's recorded LeanFinder, Loogle, grep, and LeanSearch queries
were rechecked. `rg` over Mathlib and `WeilConjectures` found only Mathlib's
`SheafOfModules.IsQuasicoherent`, `IsFiniteType` generators, and
`IsFinitePresentation`; no predicate with the Stacks three-clause definition.
`grep -rl pqf-def-coherent dag/nodes` found no other declaration. The exact
Mathlib declarations used were inspected in
`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean` and
`Mathlib/AlgebraicGeometry/Modules/Tilde.lean`.

No `STATEMENT-DISPUTED` issue or node fault was found.

## Second reading by C1

The node introduces a scheme `X`, an `\mathcal O_X`-module `F`, and three
properties.  In `Coherent.lean`, `IsQuasicoherent X F` quantifies each point
`x : X`, an affine open `U`, a commutative ring `R`, an isomorphism
`Spec R ≅ U.toScheme`, and an `R`-module `M`, then requires
`x ∈ U` and an isomorphism between `F.restrict (e.hom ≫ U.ι)` and
`AlgebraicGeometry.tilde M`; this matches the affine-local clause.  The
`IsFiniteType X F` definition quantifies `x`, `U`, and `n : ℕ`, and requires
`x ∈ U` plus an epimorphism from the finite free module indexed by
`ULift (Fin n)` onto `F.restrict U.ι`; this renders the local finite-type
clause.  `IsCoherent X F` is finite type together with, for every `U`, `n`,
and map from that finite free module to `F.restrict U.ι`,
`IsFiniteType U.toScheme (kernel f)`; this is exactly the node's requirement
that every such kernel be of finite type.  The ambient notions are Mathlib's
`AlgebraicGeometry.Scheme`, `Scheme.Modules`, restriction, `tilde`, `free`,
categorical `kernel`, and `Epi`, matching the two dependency records.

Edge cases are covered: `X` and opens may be empty, every point is quantified
vacuously when `X` is empty, `Fin 0` is permitted, and `ULift` preserves the
scheme universe.  No characteristic, Noetherian, separatedness, or finiteness
hypothesis is added.

I rechecked the recorded LeanFinder, Loogle, grep, and LeanSearch queries,
searched Mathlib and `WeilConjectures`, and inspected the source declaration
`AlgebraicGeometry.Scheme.Modules.isCoherent`.  That project declaration is
quasi-coherent plus finite presentation and therefore is not this Stacks
notion; no existing exact declaration was found.  The Stacks tag table and
source labels confirm Tags 01BV, 01B5, 01BE, and 01IA.

Two mismatches were repaired.  The node's `source.external` incorrectly said
Tag 01DW; it now records the four tags named by the statement.  The worker's
coherence clause required a single global epimorphism from a finite free
module onto each kernel, which is stronger than “the kernel is of finite
type”; it now uses `IsFiniteType U.toScheme (kernel f)`, the local definition
already given above.  The corrected module compiles cleanly with
`scompile.py`.

## Reviewer fix (R-pdc1131, stage 2)

The delivered module defined three private predicates in namespace
`AlgebraicGeometry.Scheme.Modules`: `IsQuasicoherent` (affine tilde form), `IsFiniteType`
and `IsCoherent`. Two of them restate Mathlib notions (H4/H12, one definition per notion):
finite type is Mathlib's `SheafOfModules.IsFiniteType` (locally finitely many generating
sections = local epi from O_U^n, Stacks 01B5), quasi-coherence is Mathlib's
`SheafOfModules.IsQuasicoherent` (Stacks 01BE; the tilde form of 01IA is a theorem for
schemes), already used by landed modules (`FlatModuleDescent`, `MeromorphicDenominatorIdeal`).
Worse, the private names shadow Mathlib's under dot notation on `X.Modules` (a `def`): with the
delivered module imported, the landed idiom `[M.IsQuasicoherent]` for `M : X.Modules` fails
("invalid binder annotation, type is not a class instance: Scheme.Modules.IsQuasicoherent X M"),
checked by compiling it.

Fixed module: only the genuinely new notion,
`AlgebraicGeometry.RingedSpace.IsCoherent (X : RingedSpace.{u}) (F : SheafOfModules.{u} (moduleRings X)) : Prop :=
F.IsFiniteType ∧ ∀ (U : Opens X) (n : ℕ) (f : free (R := (moduleRings X).over U) (ULift (Fin n)) ⟶ F.over U), (kernel f).IsFiniteType`
(Stacks 01BV clause by clause), on the carrier of the finite-presentation siblings
(H1 b584b4921, 173a84891). For a scheme `X`, `IsCoherent X.toRingedSpace F` typechecks with
`F : X.Modules` (checked), and Mathlib's `[F.IsQuasicoherent]`/`[F.IsFiniteType]` combine with it.
No free universes (`#print`: `IsFiniteType.{u,u,u}` throughout). The source's
`Scheme.Modules.isCoherent` (quasi-coherent + finitely presented) is a different notion
(equal on locally Noetherian schemes) and is not attached.
