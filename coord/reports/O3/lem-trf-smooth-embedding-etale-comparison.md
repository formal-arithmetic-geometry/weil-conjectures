## Worker report

Item: `lem-trf-smooth-embedding-etale-comparison`. Group O3, stage 2, 2026-10-22.

The module `Sheaf.AlgebraicGeometry.MinimalSmoothEnvelopeComparison` states all five
assertion clauses of the node. Its five theorems have `sorry` proofs. The two definitions
have explicit data. They are helpers for this node's own minimal-envelope definition and
henselian comparison; no independent notion or new node is introduced. The node changes
only in `lean` and by adding the two already-landed statement dependencies
`def-a1-relative-differentials-pullback-map` and `def-pc-module-stalk-functor`.
The primary recorded signature is the existence assertion; `lean.declarations` lists
every definition and every assertion, including the other four clauses.

The former worker's duplicate-delivery error concerned Q73's completed stage-1 split.
The current base has no Lean record for this item, and the preserved sandbox contained
only dispatcher marker files. This packet supplies the missing stage-2 statements;
it does not redeliver or change Q73's split, statement, proof, or review.

### Hypotheses and clauses

All five theorems bind `k : Type u`, `[Field k]`, and `[CharZero k]`, and use
schemes in `Scheme.{u}`. These are arbitrary scheme and field sizes after the usual
common-universe lift. Finite type of the specified structure map `p` is rendered by
`[LocallyOfFiniteType p] [QuasiCompact p]`, exactly as its dependency record requires.
No reducedness, smoothness of X, closedness of x, algebraic closedness of k, or residue
field equality with k is assumed. Explicit structure morphisms avoid supplying arbitrary
unrelated field-algebra structures. All variables and universes are explicitly bound;
`autoImplicit` is false.

1. The definition of a minimal smooth envelope is
   `Scheme.Hom.IsMinimalSmoothEnvelope p i x`. It says `IsClosedImmersion i`, `Smooth p`,
   and invertibility of the canonical differential-fibre map. Specifically take the
   existing `p.relativeDifferentialsPullbackMap i`, apply
   `RingedSpace.moduleStalkFunctor X.toRingedSpace x`, and then
   `ModuleCat.extendScalars (X.residue x).hom`. Its domain is canonically
   `κ(x) ⊗[O_M,i(x)] Ω_M,i(x)` and its target is
   `κ(x) ⊗[O_X,x] Ω_X,x`; hence `IsIso` expresses exactly the displayed differential
   isomorphism in the node. The target structure morphism is `i ≫ p`; each theorem
   identifies it with the specified structure map of X. The existing relative differential
   sheaf and universal map enforce the stated additive, Leibniz and constant relations;
   no independent differential object or unspecified map is substituted.

2. Existence after restriction and etale localization is
   `Scheme.exists_minimal_smooth_envelope`: for the supplied `x : X`, it gives an open
   `U`, `hx : x ∈ U`, a scheme M, a map q to `Spec k`, and a closed embedding i of U,
   with `i ≫ q = U.ι ≫ p` and minimality at `⟨x,hx⟩`. The stage-1 proof actually
   produces an ordinary open neighbourhood, which is an allowed etale neighbourhood;
   this is the open form already proved by Steps 1--3, rather than an extra hypothesis
   restricting which X is allowed.

3. The assertion inside every smooth envelope is
   `Scheme.Hom.exists_minimal_closed_smooth_envelope_inside`. The supplied q is smooth,
   i is a closed immersion, and `hi : i ≫ q = p` records the base field structure.
   Its output gives an ambient open V and exactly its closed preimage
   `U = i ⁻¹ᵁ V`, containing x. The intermediate `M₀` is closed in V (`IsClosedImmersion j`)
   and `i₀ ≫ j = i.resLE V U hUV` factors the original embedding. The equations with
   q and `q₀` make the factorization over k. Minimality of `q₀,i₀` supplies smoothness
   of `M₀` and the required canonical differential isomorphism.

4. The common etale neighbourhood is
   `Scheme.Hom.exists_common_etale_minimal_smooth_envelopes`. Its two given embeddings
   are minimal at the same x; `h₁,h₂` make them embeddings of the same k-scheme X.
   A specified identification between two germs is rendered by identifying their open
   representatives and composing the second embedding with that supplied identification.
   The conclusion gives U containing x, P, etale `a₁,a₂`, and the same closed immersion
   `j : U.toScheme ⟶ P`. The two squares
   `IsPullback j U.ι a₁ i₁` and `IsPullback j U.ι a₂ i₂` identify the actual inverse-image
   closed subschemes with that given U, scheme-theoretically, with the specified identity
   on U. They are not merely equalities of point sets or isomorphisms of unrelated germs.
   The common structure-map equation makes the comparison over k. The marked point is
   `j ⟨x,hx⟩`; its residue field is canonically κ(x), since j is a closed immersion.

5. The equivalent henselian assertion is
   `Scheme.Hom.minimal_smooth_envelopes_henselian_comparison`. It uses the recorded
   `Algebra.IsHenselizationAtPrime'` at the maximal ideals of the actual three stalks,
   for arbitrary supplied henselizations `H₁,H₂,Hₓ`. Here all three can be taken in
   `Type u`, the universe of those local rings; no small independent test-ring universe
   or restriction on points is introduced. Their test rings are in the same universe.
   `smoothEnvelopeHenselizationMap` is the actual composite of the localization map and
   the structural algebra map to H. The theorem supplies local, surjective quotient
   maps `b₁,b₂`, characterized by their squares with the original stalk maps to X,
   and a ring equivalence e with `b₂.comp e.toRingHom = b₁`. Thus the induced quotient
   equivalence is exactly the prescribed identification of X's henselian germ, not an
   arbitrary quotient isomorphism. The final equation explicitly makes e fix the
   images of k under the two ambient structure morphisms. Henselizations are taken as
   given objects, whose existence is provided by the pair-henselization inputs in Step 6;
   no arbitrary `Nonempty` choice defines any of these maps or rings. As the node's proof
   explains, existence of a henselian comparison does not assert algebraization of a
   separately prescribed henselian isomorphism.

6. The smooth-pair clause is
   `Scheme.Hom.exists_etale_smooth_closed_pair_retraction`. Its hypotheses are smoothness
   of both supplied structure maps, the closed immersion i, its equation over k, and
   `y : N`. It gives an affine open T containing y, affine P etale over M, a retraction
   `b : P ⟶ T.toScheme` with closed section s and `s ≫ b = 𝟙 _`, and
   `IsPullback s T.ι a i`. Thus the inverse image of N is exactly T, not an unrelated
   copy. The section restricts the given inclusion by this square. The etale map e to
   `AffineSpace (ULift (Fin r)) T.toScheme` is over T, and the displayed zero-section
   pullback identifies exactly that section as its zero fibre. The base T is an open,
   hence etale neighbourhood of N as permitted by the statement.

7. Transverse regular parameters are the actual coordinate pullbacks
   `f j = e.appTop (AffineSpace.coord T.toScheme (ULift.up j))`.
   `RingTheory.Sequence.IsRegular Γ(P,⊤) (List.ofFn f)` is full regularity on the affine
   chart. The equality on every affine open W says those coordinates generate the
   section's actual ideal `s.ker`. The quotient equivalence Q and its formula on each z
   say elimination is the actual section augmentation, not an unspecified equivalence.
   Conversely e identifies the pair etale-locally with the zero section in affine
   r-space, which adjoins the transverse parameters. Applying this clause to `M₀ ↪ M`
   from assertion 3 gives the node's passage from a nonminimal envelope to a minimal
   one; assertion 4 compares different minimal choices.

8. Preservation of specified ideals is explicit in both comparison assertions, for
   **every** `J : X.IdealSheafData` or `J : N.IdealSheafData`. In the common comparison,
   `(J.map i₁).comap a₁ = (J.comap U.ι).map j` and its second counterpart identify the
   ambient inverse-image ideals with the same ideal on the closed pair. Mathlib's
   `J.map i` is the ideal of `J.subschemeι ≫ i`, hence the inverse-image ideal under
   the ambient quotient. In the transverse assertion the first equality does the same
   for the ambient etale neighbourhood, and the second compares with extension along
   the zero-section model. Together with the augmentation quotient they assert precisely
   the required adjoining/eliminating compatibility. For an ideal originally specified
   on X inside a minimal envelope N, apply this assertion to its inverse-image ideal
   `J.map (X ↪ N)` on N. No arbitrary ambient lift is assumed preserved.

### Recorded dependency declarations used

The statement dependencies were opened at their recorded definitions and docstrings:

| Node | Module and declaration used |
| --- | --- |
| def-weil-finite-type-morphism | `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`; `...QuasiCompact`: `AlgebraicGeometry.QuasiCompact` |
| def-weil-closed-immersion | `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion` |
| def-sbc-smooth-morphisms | `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth` |
| def-weil-etale-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale` |
| def-weil-pbc-kahler-differentials | `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, `KaehlerDifferential.D`, universal differential relations |
| def-sc-relative-differential-sheaf | `WeilConjectures.AlgebraicGeometry.Modules.Differentials`: `AlgebraicGeometry.Scheme.Hom.relativeDifferentials` |
| def-sbc-affine-space | `Mathlib.AlgebraicGeometry.AffineSpace`: `AlgebraicGeometry.AffineSpace`, `AffineSpace.coord`, `AffineSpace.homOfVector`, its projection to the base |
| def-sbc-closed-immersion-ideal-sheaf | `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `AlgebraicGeometry.Scheme.Hom.ker`; `...Functorial`: `Scheme.IdealSheafData.map`, `.comap` |
| def-weil-pbc-regular-sequence | `Mathlib.RingTheory.Regular.RegularSequence`: `RingTheory.Sequence.IsRegular` |
| def-weil-pbc-henselization-at-prime | `Sheaf.RingTheory.GeneralizedHenselizationAtPrime`: `Algebra.IsHenselizationAtPrime'` |
| def-pc-base-change | `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: existing pullback and base-change conventions; `CategoryTheory.Limits.IsPullback` expresses the Cartesian closed pairs |
| def-a1-relative-differentials-pullback-map | `Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap`: `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackMap` |
| def-pc-module-stalk-functor | `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`: `AlgebraicGeometry.RingedSpace.moduleStalkFunctor` |

The recorded henselization interface is usable unchanged. No dependency record is repaired.
The source modules of all stated proof dependencies are also imported, privately when they
are used only by the proof plan. The docstrings give the corresponding Steps 1--10, including
the distinction between the right-exact conormal sequence for singular X and the short-exact
one used only for smooth N. The source PDF was read at VIII 2.3.11--2.3.13: those remarks
motivate the resolution input and do not themselves prove this comparison, exactly as Q73's
record states. The mathematical local proof is the explicit coordinate/fibre-product argument
in the DAG, with its individual Stacks references. No source or statement correction is made.

### Edge cases checked

- Empty X or N has no supplied point; the pointed assertions have no excluded existing case.
- X may be singular or nonreduced. Only the ambient differentials are assumed smooth; minimality
  uses a canonical map and does not assume a basis or smoothness of X.
- Generic and other nonclosed points are allowed. Residue fields are the actual `X.residue x`
  and stalks, never k substituted for κ(x); no algebraically closed base is used.
- If the original envelope is already minimal, the inside construction allows zero equations.
- For `r=0`, `Fin 0` is empty, the list is empty, and affine zero-space is the base. The section
  quotient is nonzero because T contains y, so full regularity of the empty list is appropriate.
- On affine opens disjoint from the section, only the generated-ideal equality is imposed.
  Full regularity is imposed on P containing the nonempty section, not on every such open.
- The Cartesian conditions remove unwanted components of the etale inverse images; mere
  agreement of residue-field fibres would not suffice. The specified identification is retained.
- All ideal equalities are for inverse-image ideals under the actual quotient maps, as in Step 10;
  the node does not claim preservation of arbitrary ambient ideals with the same restriction.

### Searches and validation

- `msearch.py leanfinder`, query: "Minimal smooth closed embeddings of a finite type scheme
  into smooth schemes have a common etale neighbourhood inducing the given identification of
  the closed subscheme". Eight generic smooth/etale/immersion results; no match.
- `msearch.py leansearch`, query: "Two minimal smooth embeddings of the same scheme have a
  common etale neighbourhood". Eight generic etale/smooth and manifold embedding results;
  no scheme-theoretic minimal-envelope comparison.
- `msearch.py loogle`, query:
  `AlgebraicGeometry.Smooth, AlgebraicGeometry.Etale, AlgebraicGeometry.IsClosedImmersion`.
  Zero hits.
- `msearch.py grep`, query:
  `minimal.*(embedding|envelope)|tubular|henselization.*quotient`, in `AlgebraicGeometry`.
  Zero Mathlib hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for minimal embeddings/envelopes,
  tubular charts and the exact node id: no declaration for this node. The resolution-invariant
  module mentions minimal-embedding independence in its proof text but supplies no construction
  or comparison theorem. Existing smooth-pair and centred-section coordinate theorems cover
  parts of the proof, not minimal-envelope existence and comparison; their interfaces were read
  and their appropriate recorded modules are imported.
- The DAG contains this item and its consumer describing the same input, not another definition
  or statement that already supplies the five assertions.
- `scompile.py` checked the delivered file as a sandbox and as its library module. The initial
  diagnostic requested a public regular-sequence import; it was added. Both then compiled
  cleanly (about 7 and 9 seconds). The final delivery dry run repeats the server check after
  the explicit dependency-import additions.

No `STATEMENT-DISPUTED` issue, statement correction, new node, or dependency module is needed.
All five theorem proofs remain `sorry`, as required in stage 2.

## Second reading by O3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
