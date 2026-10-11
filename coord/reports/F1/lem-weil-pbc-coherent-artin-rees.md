## Worker report

The module `Sheaf.AlgebraicGeometry.CoherentArtinRees` states
`AlgebraicGeometry.Scheme.coherent_artin_rees`, with a `sorry` proof, and defines no new
notion. It renders the entire node without changing its statement or dependencies.
Source checked: https://stacks.math.columbia.edu/tag/01YA (the local literature tree is
absent on this machine). The equality agrees with Lemma 30.10.3; the node additionally
spells out its immediate inclusion consequence.

Hypothesis and clause mapping:

- A Noetherian scheme: `{X : Scheme.{u}} [IsNoetherian X]`. Mathlib's class extends both
  `IsLocallyNoetherian X` and `CompactSpace X`, precisely the node's two conditions.
- A coherent O_X-module: `F : X.Modules` and
  `hF : RingedSpace.IsCoherent X.toRingedSpace F`. The moduleRings and ringCatSheaf carriers
  agree definitionally, as confirmed by compilation.
- A quasi-coherent submodule G of F: `G : X.Modules`, `g : G ⟶ F`, `[Mono g]`, and
  `hG : G.IsQuasicoherent`. A monomorphism of module sheaves is an inclusion up to the
  canonical identification with its image; it is sectionwise injective. No extra
  quasi-coherence assumption is imposed on F: the node asks coherence only.
- A quasi-coherent ideal sheaf: `I : X.IdealSheafData`, with actual module inclusion
  `I.toModulesι`. IdealSheafData is the shared affine-local encoding of exactly
  quasi-coherent ideals, with its source bridge to the kernel ideal sheaf.
- Ideal powers and ideal action: `(idealSheafPower I.toModulesι t).2` and
  `idealModuleProductι ... M`, respectively. These are the recorded formal-module node's
  shared multiplication-image constructions. At t=0 the ideal is O_X with identity
  inclusion, and its image acting on M is M, so the node's zeroth-power convention holds.
- Sectionwise intersection: `pullback (idealModuleProductι ... F) g`, embedded into F
  by `pullback.fst ... g ≫ idealModuleProductι ... F`. Limits of module sheaves are
  sectionwise, so its sections identify with the intersection inside F(W).
- A nonnegative integer constant: `∃ c : ℕ`, independent of n and W.
- All n≥c: `∀ n : ℕ, c ≤ n →`; natural subtraction `n - c` agrees with integer
  subtraction under this hypothesis.
- Equality I^(n-c)(I^c F∩G)=I^n F∩G: the first conjunct, for every `W : X.Opens`,
  equates the range of the multiplication-image inclusion on the pullback, composed
  into F, with the intersection of the ranges of I^n F→F and g on W.
- Inclusion I^n F∩G ⊆ I^(n-c)G: the second conjunct compares that same intersection
  with the range of `idealModuleProductι ... G ≫ g` on every W. Both clauses concern
  subsheaves inside the same F, not merely isomorphic abstract objects or affine sections.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`,
  `AlgebraicGeometry.IsNoetherian` (the latter bundles the former with quasi-compactness).
- `Sheaf.AlgebraicGeometry.Coherent`: `AlgebraicGeometry.RingedSpace.IsCoherent`.
- `Mathlib.AlgebraicGeometry.Modules.Sheaf`: `AlgebraicGeometry.Scheme.Modules`, its
  Abelian and limits instances; module morphisms with `.app` on opens.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`:
  `SheafOfModules.IsQuasicoherent`.
- `Sheaf.AlgebraicGeometry.CoherentFormalModule`: read `CoherentFormalModule` and
  `formalModuleQuotient` and their docstrings; its notation clause delegates to
  `Sheaf.AlgebraicGeometry.IdealModuleProductStalk`:
  `AlgebraicGeometry.Scheme.idealModuleProduct`, `idealModuleProductι`, `idealSheafPower`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`:
  `AlgebraicGeometry.Scheme.IdealSheafData.toModules`, `toModulesι`.
- The conventions dependency has no declaration; its quasi-compact convention is rendered
  by the `CompactSpace` parent of `IsNoetherian`.
- Mathlib `CategoryTheory.Limits.pullback` and `pullback.fst`, and `Set.range` / set
  intersection express existing limit and image notions; no private definition is needed.

Edge cases checked mathematically: empty X (take c=0), F=0, G=0, G=F, I=0 (take c=1 if
needed), I=O_X (take c=0), n=c, and c=0. At n=c the zeroth ideal power acts as identity.
No nonempty, nonzero, separatedness, finite-type, or affine-only condition is added.
The universe u is explicitly bound and shared by X and its module sheaves.

Searches made (also recorded by msearch.py in searches.jsonl):

- LeanSearch, query `Artin Rees lemma for coherent sheaves on a Noetherian scheme`:
  service unavailable (Internal Server Error); no verdict inferred from its failure.
- LeanFinder, query `Artin Rees for coherent sheaves I^n F intersection G equals
  I^(n-c) times I^c F intersection G`: eight hits, including
  `Ideal.exists_pow_inf_eq_pow_smul`, stable-filtration statements and local cohomology;
  all are ring/module statements, not this scheme-sheaf statement.
- Loogle, query `Ideal.exists_pow_inf_eq_pow_smul`: one hit, the ring/module Artin-Rees
  lemma, with its full signature checked; not a match for the node's objects.
- msearch grep, query `Artin.Rees|artinRees|exists_pow_inf_eq_pow_smul`: six Mathlib
  hits in RingTheory/Filtration, AdicCompletion/Exactness and ReesAlgebra; no scheme lemma.
- rg of `Artin.Rees|artin.?[Rr]ees|lem-weil-pbc-coherent-artin-rees` in upstream
  WeilConjectures and project lean/Sheaf: upstream has a proof comment using Artin-Rees;
  project has proof comments in AssociatedPrimePowerQuotient and
  SmoothAtPrimeArtinianLifting. No existing declaration of this statement.
- rg of `ideal.*[Pp]ow|ideal.*[Mm]ul|idealPower|idealProduct` in project Lean found the
  shared ideal product/power definitions, which are reused, not rewritten.
- rg of `coherent_artin_rees` in dag/lean_names_upstream.json, upstream WeilConjectures,
  Mathlib, and project Lean found no name collision.

Server compilation via scompile.py completed cleanly in 2.7 seconds. All theorem proofs
are `sorry`. No disputed statement or node fault was found. No new or dependency module
is required.

## Second reading by F1

Independent reading of the node copy and CoherentArtinRees.lean, with all five
statement-dependency nodes and their recorded source declarations open. The local Stacks
.tex tree is absent; I read the actual coherent.tex from
https://raw.githubusercontent.com/stacks/stacks-project/master/coherent.tex, at
`lemma-Artin-Rees`, and its preceding section `section-coherent-quasi-compact`, as well as
https://stacks.math.columbia.edu/tag/01YA. The section imposes no additional standing base,
characteristic, separatedness, or finite-type hypothesis. Its lemma introduces precisely
the four objects below. The node adds the immediate inclusion consequence of the equality;
this is valid by multiplying the inclusion of the intersection into G.

Object, hypothesis and conclusion inventory, with Lean rendering and verdict:

1. Scheme X, locally Noetherian and quasi-compact: `{X : Scheme.{u}} [IsNoetherian X]`.
   PASS. In Mathlib.AlgebraicGeometry.Noetherian, IsNoetherian extends exactly
   IsLocallyNoetherian and CompactSpace. The recorded pqf-def-locnoeth declaration uses
   every affine ring Noetherian, equivalent to an affine Noetherian cover by its recorded
   cover theorems. The scheme-conventions dependency fixes no separate notion.
2. Coherent O_X-module F: `F : X.Modules` and
   `hF : RingedSpace.IsCoherent X.toRingedSpace F`. PASS. I read pqf-def-coherent and
   Sheaf.AlgebraicGeometry.Coherent: this predicate requires finite type and finite-type
   kernels of every finite-free map on every open. The ringed-space and scheme module
   carriers coincide, and the finite-free indices use ULift (Fin n), including n=0.
3. Quasi-coherent submodule G of F: `G : X.Modules`, `g : G ⟶ F`, `[Mono g]`,
   `hG : G.IsQuasicoherent`. PASS. Modules.Sheaf defines exactly sheaves of modules over
   X.ringCatSheaf, with sectionwise linear morphisms. A mono identifies G with its
   subsheaf image, rather than adding a finiteness condition or selecting a special
   inclusion. Quasicoherent.lean's IsQuasicoherent requires local free presentations,
   the shared quasi-coherence notion in the dependency, not an unrelated predicate.
4. Quasi-coherent sheaf of ideals I: `I : X.IdealSheafData`. PASS. I read Mathlib's
   affine-local ideal-data description and the upstream IdealSheaf.Module bridge.
   `toModules` is the kernel of the map to the closed-subscheme pushforward and
   `toModulesι` is kernel.ι. The range on affine opens is precisely the specified ideal,
   with injectivity on every open. This represents arbitrary quasi-coherent ideals;
   there is no additional invertibility or properness requirement.
5. Ideal powers and multiplication-image subsheaves: `(idealSheafPower I.toModulesι t).2`
   and `idealModuleProductι ... M`. PASS. The recorded CoherentFormalModule module
   delegates these notions to IdealModuleProductStalk; I read its definitions themselves.
   The latter is image.ι of the tensor multiplication map. Powers start with the unit
   module and identity at 0, the given ideal at 1, and recursively multiply at n+2.
   Thus I^0 M has full image M, and every positive power has the node's meaning. No
   private product definition, affine-sections substitute, or hollow data is used.
6. Sectionwise intersection inside F: the pullback of
   `idealModuleProductι (idealSheafPower I.toModulesι c).2 F` and g, mapped into F via
   `pullback.fst ... g ≫ idealModuleProductι ... F`. PASS. The module forgetful functor
   to presheaves is right adjoint (Modules.Sheaf), hence preserves this limit;
   pullbacks of injective linear maps identify with the intersection of their ranges.
7. One integer c>=0 independent of n and the open: `∃ c : ℕ`. PASS. Naturals encode
   exactly nonnegative integers; there is no positivity condition.
8. Every integer n>=c: `∀ n : ℕ, c ≤ n → ∀ W : X.Opens`. PASS. This covers all
   relevant integers since c>=0, and subtraction n-c is exact under the bound.
9. Equality I^(n-c)(I^c F intersect G)=I^n F intersect G: the first Set.range equality.
   PASS. Its left map multiplies on the pullback module before composing its inclusion
   into F. Its right side intersects the ranges of I^n F's inclusion and g on W.
   Quantification over all opens makes this exactly equality of subsheaves, not merely
   global sections or abstract isomorphism.
10. Inclusion I^n F intersect G into I^(n-c)G, inside F: the second conjunct,
    `Set.range (...) ∩ Set.range (g.app W) ⊆ Set.range ((idealModuleProductι ... G ≫
    g).app W)`. PASS. Composition with g gives the intended ambient F. Combining both
    clauses under each W is logically equivalent to the two sheaf assertions for each n.

Edge cases: empty X admits c=0; no Nonempty hypothesis appears. Zero F or zero G gives
zero intersections and c=0 works. G=F gives the product-of-powers equality. For I=0,
c=1 works; the case n=c uses exponent 0 on the left and on G. For I=O_X, c=0 works.
At c=0 and n=0 both expressions are the image of G inside F. Empty opens are included
by `∀ W : X.Opens`. No index set occurs in the signature; the proof's empty finite
cover is expressly handled by its maximum-zero convention. No characteristic restriction
occurs. The explicit arbitrary universe u covers schemes and their module sheaves in
that universe; there is no independent smaller test-object universe or unbound binder.

Independent searches (recorded in searches.jsonl): LeanFinder query
`uniform stabilization of intersections of ideal powers with subsheaves on a scheme`
returned eight hits, notably Ideal.exists_pow_inf_eq_pow_smul and ideal-sheaf lattice
facts. The Artin-Rees hit quantifies over a commutative ring and a finite module, not
scheme sheaves, so it is only the existing affine proof leaf. Loogle query `"Artin"`
returned unrelated String startInclusive declarations; it establishes no mathematical
match. LeanSearch query `There is a uniform integer bounding intersections with ideal
powers for coherent sheaves` failed with Internal Server Error; no absence verdict is
inferred from this failure. Independent rg for `pow.*inf|inf.*pow|[Aa]rtin|[Rr]ees` in
the AlgebraicGeometry trees, followed by the precise patterns
`exists_pow_inf_eq_pow_smul|pow_inf|Artin.Rees|artin.?[Rr]ees|coherent_artin_rees` across
all upstream WeilConjectures, project lean/Sheaf, Mathlib Filtration and the upstream
name map found only ring-theoretic Artin-Rees and proof comments. No duplicate scheme
statement exists. The actual shared power, tensor-image and ideal bridge definitions
were read, rather than inferred from declaration names.

No mismatch found; no Lean, signature, dependency or node correction was needed. There
are no new definition nodes or dependency modules in this delivery. The sole theorem
proof is `by sorry`; the file defines no data and proves nothing. Both docstrings name
the source and blueprint id, and the theorem docstring follows all four proof steps:
finite affine cover and finiteness, uniform maximum, quasi-coherent intersection kernel,
and local equality followed by inclusion. The single import supplies the recorded
formal-module notation and the other dependency declarations. No local notation,
private declaration, let/show in the signature, or unbound universe/variable occurs.
Only this independent-reading section was appended; the correct module was left intact.

Validation: scompile.py compiled the unchanged module on the server in 2.6 seconds with
exit code 0 and no disallowed warning. The recorded lean.statement was checked verbatim
against the file's signature, and every Lean line is at most 100 characters. deliver2.py
--no-push returned OK: the delivery passes preflight and compiles.
