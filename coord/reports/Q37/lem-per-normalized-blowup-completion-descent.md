## Worker report

The module `Sheaf.AlgebraicGeometry.NormalizedBlowupCompletionDescent` states
`AlgebraicGeometry.exists_normalizedBlowup_tower_of_completion`, with `sorry` as its
whole proof. It introduces no definitions, instances or additional theorems. The
item node changes only in `lean`. No statement correction, new node, dependency
repair or disputed statement is needed.

Source read: `literature/stacks-project/resolve.tex`, lemma
`lemma-normalized-blowup-completion` (Tag 0BGA), its induction proof, and lemma
`lemma-port-regularity-to-completion` (Tag 0BG6), especially clauses (1) and (3).
The module docstring reproduces the node's five proof steps, including the Tag
0BG9 normalization comparison and regularity descent. Proofs remain for stage 3.

Clause-by-clause rendering:

- A commutative Noetherian local domain is `(A : Type u) [CommRing A]
  [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]`. Its maximal ideal is
  `IsLocalRing.maximalIdeal A`; no additional maximal ideal is chosen.
- The completion is exactly `AdicCompletion (IsLocalRing.maximalIdeal A) A`.
  Its normal-domain hypothesis is the two instances `IsDomain` and
  `IsIntegrallyClosed` on this very ring. Neither excellence nor a dimension
  assumption is imposed.
- A finite sequence of length `n : ℕ` is `Z : Fin (n + 1) → Scheme.{u}`, with
  adjacent arrows `bZ i : Z i.succ ⟶ Z i.castSucc` for `i : Fin n`.
  `pZ i` is its structure map to the completion's spectrum. `hZ₀ : IsIso (pZ 0)`
  identifies the degree-zero scheme with that spectrum; `hpZ` makes every
  adjacent arrow commute with the structure map. This is a diagram encoding
  of a sequence based at the specified spectrum, allowing its degree-zero
  object to carry the given identification instead of requiring definitional
  equality of scheme records. It neither constrains nor changes the sequence.
- Every given arrow is proper: `IsProper (bZ i)` in `hZ`.
- Its center is `y : Z i.castSucc`, closed by
  `hy : IsClosed ({y} : Set (Z i.castSucc))`.
  `pZ i.castSucc y = IsLocalRing.closedPoint ...` puts it over the completion's
  closed point, rather than merely somewhere over Spec A.
- The center has its reduced induced structure: the ideal sheaf `J` is
  required to equal `Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩`.
  The ordinary blowup and its map are the existing `J.blowup` and `J.blowupMap`.
- Normalization is in the function field, exactly as the statement specifies:
  the existential `IsIntegral J.blowup` supplies the domain of the existing
  `Scheme.normalization` construction. The isomorphism
  `e : Z i.succ ≅ J.blowup.normalization` and the equation
  `e.hom ≫ J.blowup.fromNormalization ≫ J.blowupMap = bZ i` retain the actual
  normalized blowup morphism. There is no arbitrary map standing in for it.
  The integral witness expresses the well-typedness inherent in normalization
  in the function field; it is not an excellence, normality or finiteness
  assumption on the ordinary blowup.
- The conclusion supplies `X`, `bX`, and `pX` with the same index sets and
  orientation, with `IsIso (pX 0)` and the same adjacent structure equations,
  over `Spec (.of A)`. Its closed reduced centers, lying over
  `IsLocalRing.closedPoint A`, and proper normalized blowup equations repeat
  precisely the corresponding given-tower clauses.
- The base-change comparison is a family `c i : Z i ⟶ X i` for which
  `IsPullback (c i) (pZ i) (pX i) (Spec.map (CommRingCat.ofHom (algebraMap A ...)))`
  holds for every level. This square includes commutation with the specified
  structure morphisms and the full universal property. Uniqueness of limits
  gives a unique isomorphism from `Z i` to the chosen fibre product with both
  projections respected. The equations
  `c i.succ ≫ bX i = bZ i ≫ c i.castSucc`, together with `hpZ` and the analogous
  equations for `pX`, ensure those isomorphisms identify all adjacent tower
  arrows; composites then commute as well. Thus this is an isomorphism of
  sequences over the completion, not just unrelated endpoint isomorphisms or
  a commutative square without its universal property.
- The last clause is exactly
  `IsRegularScheme (Z (Fin.last n)) → IsRegularScheme (X (Fin.last n))`.
  The recorded scheme-regularity definition includes local Noetherianity.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, the abbreviation
  for every ideal being finitely generated.
- `Mathlib.RingTheory.AdicCompletion.Basic`, with `LocalRing` and its algebra
  imports: `AdicCompletion`, its canonical `algebraMap`, and the local-ring
  instance for completion at the maximal ideal of a Noetherian local ring.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  used with `IsDomain` for the recorded normal-domain clause.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`; the map of spectra
  is that of the canonical completion ring homomorphism, with no replacement
  by a freely chosen completion or an arbitrary morphism.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`.
- `WeilConjectures.Blowup.Gluing`:
  `AlgebraicGeometry.Scheme.IdealSheafData.blowup` and `.blowupMap`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`:
  `AlgebraicGeometry.Scheme.normalization` and `.fromNormalization`, whose
  integral-scheme input and full signatures/docstrings were read.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs`:
  `CategoryTheory.IsPullback`, the limit-cone universal property for the
  recorded fibre-product notion. The recorded `Limits.pullback` and both
  projections were also read; using the universal property permits the
  comparison to be stated without silently choosing independent isomorphisms.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`:
  `AlgebraicGeometry.IsRegularScheme = IsLocallyNoetherian X ∧ IsRegular X`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`:
  `Scheme.IdealSheafData.vanishingIdeal`. Its docstring explicitly identifies
  its quotient with the reduced induced scheme structure of the closed set.

All statement dependencies are public imports directly or through the specific
construction modules that define them. All available recorded proof-dependency
modules are imported without `public`: `WeilConjectures.Blowup.FlatBaseChange`,
`.Complement`, `.Proper`; `Sheaf.AlgebraicGeometry.ReducedNormalization`;
`Sheaf.RingTheory.RegularRingFaithfullyFlatDescent`; and the Mathlib flatness,
surjectivity, completion-flatness and faithfully-flat algebra modules.
`thm-nagata-blowup-flat-base-change` has no `lean` or `mathlib_match`, but its
closed upstream audit names `blowupFlatBaseChangeIso` in
`WeilConjectures.Blowup.FlatBaseChange`. The old local source lacks this module;
its current source, full signature and docstring were read using
`scompile.py --source WeilConjectures.Blowup.FlatBaseChange`, and it imports
successfully in this delivery. `lem-per-normalization-completion-base-change`
currently has neither a recorded module nor a closed upstream declaration:
it is only a proof input, introduces no object needed to type this statement,
and thus has no module to import yet. Its use is preserved in the proof plan.

Edge cases checked before writing and again on the final signature:

- `n = 0`: `Fin n` is empty, so there are no arrows or centers to choose;
  `Fin (n + 1)` still has its base object, `Fin.last n = 0`, and the statement
  still supplies the identity-spectrum pullback and regularity descent.
- Already regular completions and identity towers impose no spurious positive
  length or singularity hypothesis.
- Dimension zero / A a field is not excluded. The identity tower is included.
  An ordinary blowup that is empty cannot be normalized in its function field
  by the integral-scheme construction; this is already inherent in the node's
  explicit function-field normalization convention, not an extra nonempty-
  center-complement hypothesis added to the statement.
- No empty endpoints are manufactured by replacing normalization in the
  function field with componentwise normalization of an empty scheme.
- A closed point with a nontrivial finite residue extension is allowed:
  only its image equals the base's closed point; no rational-point or residue-
  field-isomorphism hypothesis is imposed on that point.
- All schemes and A use the common arbitrary universe `u`, so completion and
  finite blowups stay in it. No test family in a smaller independent universe
  or universe equality is introduced; all variables and universes are explicit.

Searches for an existing statement (2026-10-18 UTC):

- `msearch.py ... leanfinder "A sequence of normalized blowups at closed points
  over a completed local domain descends to the local domain"`: eight hits,
  including adic completions of Dedekind fields, Weierstrass factorization and
  `Scheme.Hom.normalizationDesc`; none states descent of a point-blowup tower.
- `msearch.py ... loogle '"normalization", "completion"'`: zero hits.
- `msearch.py ... grep 'normalized.*[Bb]lowup|blowup.*[Cc]ompletion'`: zero hits.
- `rg` in `WeilConjectures/` and `lean/Sheaf/` for normalized blowups and blowup
  towers found componentwise normalized blowup calculus, log/monoscheme towers,
  excellent quasi-projective normalized blowups and the excellent-surface
  theorem. None states this completion-descent assertion. The componentwise
  calculus uses reducedNormalization; this node explicitly uses normalization
  in the function field and already records that exact upstream construction.
- `grep -rn 'lem-per-normalized-blowup-completion-descent'
  /home/ubuntu/weil-src-slopmaster2/WeilConjectures`: zero hits.
- Declaration-name search and the actual compile found no duplicate of
  `exists_normalizedBlowup_tower_of_completion`.

Validation: `scompile.py Q37 lem-per-normalized-blowup-completion-descent
<module path>` passed the sandbox and library compilations (2.1 s and 2.4 s),
without errors or warnings. Delivery dry-run results are recorded below after
preflight. No global build or direct Git command was run.

## Second reading by Q37

The dispatcher explicitly forbids starting another agent, so this section
records the writer's second pass, not an independent-worker certification;
the maintainer's independent delivery review remains necessary. I reopened the
item and final module and checked each premise and clause against the mapping
above. The base identification `IsIso (pZ 0)` and its descended counterpart are
part of the diagram encoding; no base or structure morphism is forgotten.
The ordinary blowup uses the radical vanishing ideal of the closed singleton,
not just an ideal with the right support. The normalization is the recorded
function-field construction, not reducedNormalization. Every descended arrow
is proper. Pullback squares at every level plus arrow commutation give the
whole tower comparison. The regularity implication is inside the same
existential choice of tower, and includes length zero. No mismatch or statement
change was found in this pass. All binders are explicit and the sole postponed
proof belongs to the item itself.

Delivery validation: `deliver2.py Q37 lem-per-normalized-blowup-completion-descent
--no-push` printed `OK (dry run): commit 8326e0cb56 passes the preflight and
compiles; nothing pushed`. The wrapper completed its shared-fetch wait itself.
