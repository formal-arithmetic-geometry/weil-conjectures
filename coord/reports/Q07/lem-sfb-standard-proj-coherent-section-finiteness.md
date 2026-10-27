## Worker report

The module `Sheaf.AlgebraicGeometry.StandardProjCoherentSectionFiniteness` states
`AlgebraicGeometry.Proj.standardProjCoherentSectionFiniteness`, with its proof `sorry`.
It introduces no definition and proves nothing. The source read is
`literature/stacks-project/coherent.tex`, lemma-coherent-on-proj (0AG6), opening
Noetherian assertion and (4) for k=0, together with the reduction to
lemma-coherent-projective (01YS), proof of (5).

Hypothesis and conclusion correspondence:

- The nonnegatively graded commutative ring is `{S : Type u} [CommRing S]`,
  `𝒜 : ℕ → AddSubgroup S`, and `[GradedRing 𝒜]`. GradedRing includes the internal
  direct-sum decomposition, so all scalars are finite sums of homogeneous scalars.
- The degree-zero Noetherian hypothesis is `[IsNoetherianRing (𝒜 0)]`, using the
  existing degree-zero ring and algebra structures of a graded ring.
- Generation as an S_0-algebra by finitely many degree-one elements is exactly
  `hgen : ∃ (r : ℕ) (f : Fin r → S), (∀ i, f i ∈ 𝒜 1) ∧
  Algebra.adjoin (𝒜 0) (Set.range f) = ⊤`. The case r=0 is permitted.
- The scheme X is exactly the existing `Proj 𝒜`.
- The first conclusion is `IsNoetherian (Proj 𝒜)`. Mathlib's
  `isNoetherian_iff_of_finite_iSup_eq_top` and
  `isNoetherian_iff_of_finite_affine_openCover` identify this with the asserted
  finite Noetherian affine cover. In particular, this includes quasi-compactness;
  merely locally Noetherian would not express the node.
- Every coherent module is quantified by `∀ (F : (Proj 𝒜).Modules),
  Scheme.Modules.IsQuasiCoherentFiniteType F → ...`. This is the unchanged
  recorded predicate of pqf-def-coherent. On the Noetherian scheme asserted by
  the first conclusion, Stacks 01XZ (1) iff (2) identifies this with coherence
  in the finite-type plus finite-type-kernels sense. This does not add a
  Noetherian hypothesis: the conclusion establishes Noetherianity from hgen
  and the Noetherian degree-zero ring.
- The tensor twist F(n) is literally `F ⊗ twist 𝒜 (n : ℤ)`, with the published
  scheme-module tensor and the published shifted-module twist.
- Nonnegative graded sections are literally the existing Mathlib direct sum
  `⨁ n : ℕ, Γ(F ⊗ twist 𝒜 (n : ℤ), ⊤)`. There is no truncation bound omitted and
  no finite-index replacement for the infinite sum.
- Its S-action is not an extra hypothesis or an arbitrary unspecified action.
  The conclusion supplies a Module structure m and fixes its action on every
  homogeneous scalar s of degree e and every component section t of degree n:
  s applied to `DirectSum.of ... n t` is the degree-(n+e) inclusion of t multiplied
  by `F ◁ twistMul (n : ℤ) hs`. `twistMul` is the existing morphism multiplying
  a twist by s/1, the canonical section of O(e). This is the same multiplication
  as the canonical tensor comparison in `standardProjTwistTensor`; it avoids
  asking for an extra degree-one covering hypothesis. The `eqToHom` only
  transports the equality `(n:ℤ)+(e:ℤ) = ((n+e):ℤ)`. Additivity of the Module
  structure and the graded decomposition determine its action everywhere from
  these equations. Thus the existential structure specifies the canonical action
  completely; it is not a choice of a conveniently finite action.
- Finite generation is `@Module.Finite S (...) _ _ m`, explicitly for the same
  action m whose homogeneous formula was just specified.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, its abbreviation as
  `IsNoetherian R R`, and `isNoetherianRing_iff_ideal_fg`.
- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`:
  `AlgebraicGeometry.Proj` and `AlgebraicGeometry.projIsoSpec`; the homogeneous
  basic opens are the existing `ProjectiveSpectrum.basicOpen`/`Proj.basicOpen`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`,
  and the equivalence with a finite affine Noetherian cover.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  `AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType`, whose full
  definition is `SheafOfModules.IsQuasicoherent F ∧ SheafOfModules.IsFiniteType F`.
  This is the live pqf-def-coherent record and is used without modifying it.
  Stacks 01XZ identifies it with coherence on a locally Noetherian scheme;
  Stacks 0AG6 supplies the Noetherian Proj in precisely this setting.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules`:
  `Proj.twist`, `Proj.twistMul`, and `Proj.unitToTwistZero`. The twist is the real
  locally-fraction sheaf, and twistMul is the actual multiplication morphism.
- `Sheaf.AlgebraicGeometry.StandardProjTwistTensor`: `Proj.standardProjTwistTensor`,
  with its public tensor dependencies, canonical twist comparison, and fraction
  characterization. This identifies the multiplication used in the statement
  with that named in the node.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` is publicly
  imported through that dependency, as recorded by def-pur-sheaf-tensor-product;
  the statement uses the existing tensor on scheme modules, not a new tensor.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, defined as finite
  generation of the top submodule for the supplied Module structure.

All published proof-dependency modules are imported without `public`, as required.
The docstring follows all six proof steps, including the polynomial quotient,
Noetherian quotient charts, projection/twist comparison with homogeneous action,
Serre-vanishing tail surjection, finite free polynomial section module, and the
finite union of low-degree and high-tail generators. No proof or proof dependency
in the JSON is changed.

Edge cases checked against the actual signature:

- Empty Proj, including the zero ring and rings with no positive-degree part:
  no point, nonempty, nonzero, or positive-rank hypothesis occurs. The section
  groups are zero, so their direct sum has the canonical zero action and the
  empty generating family. The scheme is Noetherian with an empty cover.
- F=0 likewise gives zero section groups in every degree and the empty family.
- r=0 is allowed by `Fin r` and the existential generator hypothesis.
- The degree n=0 is included; e=0 is also included in the homogeneous action
  equations, fixing the action of all degree-zero scalars.
- Nilpotent homogeneous generators and zero homogeneous scalars are allowed;
  there is no nonzero-element or domain assumption.
- The scheme and its module carrier use the published common universe u; no
  test-algebra universe, extra equality of universes, or Type-0 restriction occurs.
- The proof's b=0 case has no low generators, and r>=1 is achieved only in the
  proof by adding zero generators, never imposed in the theorem's hypotheses.

Searches actually run with msearch.py (Q07, this item):

- LeanFinder: "For a standard graded ring with Noetherian degree zero, the direct
  sum of nonnegative twisted global sections of a coherent sheaf on Proj is a
  finite module". Eight hits included Proj locally-of-finite-type, homogeneous
  localization finite type, sheaf finite-type predicates, and degree-zero
  Noetherianity. None asserts this section-module finiteness theorem.
- Loogle: `AlgebraicGeometry.Proj, Module.Finite`. Zero hits.
- Mathlib grep: `coherent.*Proj|Proj.*coherent|twist.*section`, restricted to
  AlgebraicGeometry/ProjectiveSpectrum. Zero hits.
- LeanSearch: "The nonnegative graded module of all twisted global sections of a
  coherent sheaf on a Noetherian standard Proj is finitely generated". Eight hits
  on sheaf generating sections, module Noetherianity given finiteness, and Proj
  multiplication; none is an exact match.
- rg over the prescribed upstream WeilConjectures and Sheaf trees, by item id,
  `standardProjCoherentSection`, and `nonnegativeTwistedSections`: only the
  downstream FiniteGradedModuleSectionTail docstring cites the item, with no
  declaration for this theorem. Broader standard-Proj/graded-section searches
  found the existing twist comparison, which is reused.

## Repair of H13

The returned immutable head 0ac1ae533c85 replaced the landed pqf-def-coherent
record and would orphan its existing CoherentFiniteType module. I used the
maintainer's explicit alternative: the item now imports and uses the unchanged
live `Scheme.Modules.IsQuasiCoherentFiniteType` declaration. The dependency node
copy has been removed from this packet. No dependency module or record is
modified, so the existing consumers retain their imports and declarations.
There is no change to the item's natural-language statement or dependencies.

I opened Stacks coherent.tex, lemma-coherent-Noetherian (01XZ), lines 2225ff:
for every module on a locally Noetherian scheme, coherence is equivalent to
quasi-coherence and finite type. I also reread lemma-coherent-on-proj (0AG6),
whose opening establishes that this Proj is Noetherian. Therefore changing the
Lean coherence predicate as requested preserves exactly the mathematical
quantification over F. Empty Proj and F=0 remain covered. All other hypotheses,
the homogeneous multiplication equation, and the finite-generation conclusion
are identical to the independently checked returned statement.

Validation: repaired scompile.py checks passed cleanly for the sandbox module
(3.7s) and the actual library module path (8.2s), with no errors or non-sorry
warnings. The node differs from the current read clone only in lean; its
recorded signature equals the file verbatim, every Lean line is at most 100
characters, and exactly one named theorem proof is sorry.

## Delivery gate diagnostic

The repair note is stage 1, state released, demanding a re-split of the 4985-character
proof. However, the live node already carries Q09's stage-1 split and a PASS review
by L, recorded as merged at 05:11 on 2026-10-22 in coord/ledger.md. Its statement
and proof are not ours to resplit in stage 2. The standing stage-1 brief explicitly
says live split-and-reviewed nodes win and are never split. This packet preserves
that proof verbatim and performs only the authorized stage-2 record changes.
The saved packet's initial dry run passed at 1748f0b6630, confirming that the
old stage-1 gate failure does not recur. The H13 repair described above was
then applied despite that mechanical pass. No re-split, tool modification,
or exception was needed; the repaired packet receives a fresh dry run.

## Self-check of repaired statement

Reread the node and complete Lean signature. The single universe u, grading,
Noetherian degree-zero ring, finite degree-one algebra generation, Noetherian
Proj conclusion, tensor twists in every nonnegative degree, canonical action
on every homogeneous scalar, and finiteness for that same action agree clause
by clause. The one changed predicate is equivalent by 01XZ under the first
conclusion, as detailed above. The old dependency-record overwrite is absent.
The only proof remains the named theorem's `sorry`; no definition was added.

## Second reading by Q07

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
