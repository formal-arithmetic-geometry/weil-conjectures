# HomogeneousLocalization.exists_away_scalarExtension_equiv

## Reason

The proof needs section variables and an R-algebra structure on the homogeneous localization
of the tensor algebra, obtained by composing its S-algebra map with R → S. It also needs the
corresponding scalar tower. These are private local instances, confined to the Construction
section. All new definitions and lemmas are private and fully proved. The static interface
checker classifies added section/variable/include commands as a visible-context change and
requires this record. No existing statement, definition, visibility or import is changed.

## Old

The namespace had no auxiliary construction section or local instances:

```lean
namespace HomogeneousLocalization

```

## New

Inserted immediately after the existing namespace command:

```lean
section Construction

variable {R : Type u} {S : Type v} {A : Type w}
variable [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
variable {d : ℕ} {f : A} (hf : f ∈ 𝒜 d)

private local instance scalarExtensionAlgebra :
    Algebra R (Away (fun n ↦ (𝒜 n).baseChange S) (1 ⊗ₜ[R] f)) :=
  ((algebraMap S _).comp (algebraMap R S)).toAlgebra

private local instance scalarExtensionTower :
    IsScalarTower R S (Away (fun n ↦ (𝒜 n).baseChange S) (1 ⊗ₜ[R] f)) :=
  .of_algebraMap_eq' rfl

```

The private helper definitions and lemmas follow in the same section, ending at
`end Construction` before the original theorem. `include hf in` applies only to the three
private helper lemmas whose types omit the proof of homogeneity. The original theorem keeps
its complete signature, including `hd`; its body is now a proof. The local instances are not
active when the original public theorem is declared and are not exported as instances.

## Users

`tools/downstream.py Sheaf.RingTheory.HomogeneousLocalizationScalarExtension --uses
HomogeneousLocalization.exists_away_scalarExtension_equiv` lists one importing module and
only the item's declaration as a textual use. The importer was read in full: it has a sorry
proof, imports this theorem privately, and none of its statements uses a new helper.

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.HomogeneousLocalizationScalarExtension | K9 | Proof completed; only private helpers and local instances added. |
| Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension | unclaimed | Existing import and signatures unchanged; no adaptation required. |

No target statement uses a new definition. No definition is repaired, and no target statement
review is reopened.

## Status

landed 20261018T062826-L-661303 2026-10-18 (merge of deliver/K9/Sheaf.RingTheory.HomogeneousLocalizationScalarExtension)
