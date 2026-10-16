## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteCoefficientRestrictionForgetIso_linear`
with its existing statement unchanged. The public additive comparison and module restriction
isomorphism keep their definitions and signatures. Added only proved private helpers and the
proof-only `import all Sheaf.Paper.FiniteDiscreteRestrictionEncoding`.

The proof reuses that module's existing private `encodingPushforwardIso` and `push_action`
constructions, which already implement scalar compatibility from the existing coefficient-unit
lemma. Naturality of `hG` proves compatibility with the inverse encoding's forgetful isomorphism.
The equivalence units then identify the fully faithful lift's underlying map with the particular
normalized comparison in this item. `Mod.act_hom` supplies its linearity. Private helpers perform
these checks explicitly; no copy of the existing action calculation was added. A local
semireducibility attribute opens the coefficient equivalence only in this module's elaboration.

The local proof elaboration commands are documented in
`coord/changes/finite-discrete-coefficient-restriction-proof-settings.md`. No consumer adaptation
is needed; existing public signatures and definitions remain identical.

Updated the item's node proof, proof dependencies and proof origin to record this reuse and
normalization argument. The unit's prescribed route is unchanged. Empty schemes, the zero ring
and arbitrary coefficient rings require no extra hypotheses.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteCoefficientRestrictionForgetIso_linear`
(node `lem-weil-pbc-finite-discrete-restriction-linearity`).

Original item holes: 1. Item holes left: 0. Holes added: 0. Split off: 0.
Every private helper is proved. This is a proof from existing declarations, not a decomposition.
The reused construction still depends on the existing
`AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteCoefficient_coefficientUnit_pushforward`
(node `lem-weil-pbc-finite-discrete-coefficient-sections`); that obligation is unchanged and is
not a newly introduced hole.

The item compiled locally without errors or warnings via `lcompile.py`. The unchanged direct
consumer `Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence` also compiled against
the sandbox item (15.7 seconds for the item, 10.9 seconds for the consumer). The delivery dry
run checks the declarations and axioms. No existing consumer needed adaptation.

## No longer needed

No imports or modules were pruned. The node
`def-weil-pbc-coefficient-derived-functor-api` is no longer a mathematical proof dependency;
its public module import remains needed for the existing fixed profinite-instance interface.
The original public imports remain used by the encoding and the fixed profinite instance. The added proof import reuses existing constructions.
The generic private normalization lemmas add no proof obligations to the DAG.

## Where the brief, the DAG or earlier work was wrong

The local shared snapshot lacked this assigned module and node although both were present on
the project server. Their current versions were read from the server into the permitted sandbox;
the shared repository was not changed.

The old proof plan cited only definitions. The scalar-action calculation was already implemented
in `FiniteDiscreteRestrictionEncoding`: its named private construction is reusable with Lean's
proof-only `import all`. The remaining work here was the explicit normalization through `hG`,
the forgetful comparisons and the encoding units. The updated node names both that construction's
module and its existing coefficient-unit obligation. No mathematical statement was corrected.

## Second reading by D2

1. **Existing interfaces: PASS.** Compared the entire delivered Lean file with the current
   read-only repository file. The signatures of the two existing definitions and the linearity
   theorem, their visibility, the variable block, and both existing definition bodies are byte
   for byte unchanged. The diff adds a proof-only `import all`, local elaboration commands,
   eight private proved helpers, and the proof replacing the single `sorry`. The change record
   documents the local commands. No target or consumer statement changes.

2. **Proof and trust: PASS.** Independently compiled the delivered item with `lcompile.py`:
   no errors or warnings. Read all helpers and the final proof. `inverseForgetIso_unit` expands
   the composite equivalence unit and uses the identity underlying counit of scalar restriction.
   `inverseForgetIso_pushforward` checks the sheaf map sectionwise, then uses naturality of
   `eqToIso hG` on the identity-underlying module comparison supplied by `push_action`.
   In the final proof, full faithfulness produces a module morphism; naturality, cancellation of
   the invertible forgetful component, and the source/target unit identities prove `he`.
   Expanding the unchanged normalized comparison gives `he0`, hence `he'` identifies its exact
   underlying map with that morphism. Only then does `Mod.act_hom` establish linearity.
   No arbitrary existence witness is introduced: the private definitions construct their data
   from the existing encoding and fully faithful functors. Scratch `#print axioms` checks of
   every delivered declaration show only `propext`, `Classical.choice`, `Quot.sound`, and, in
   the direct-image compatibility and its users, the existing `sorryAx` dependency from
   `finiteDiscreteCoefficient_coefficientUnit_pushforward`. There is no new `sorry`, axiom,
   unsafe implementation, or hollow definition.

3. **Split statements: PASS (none).** No statements or holes were split off. All eight new
   private helpers are proved; they express the construction, forgetful naturality, or elementary
   equivalence normalization needed by this proof. The imported `encodingPushforwardIso` is
   explicitly constructed using `G.mapIso` on identity-underlying maps; it does not select an
   arbitrary witness from the imported inverse-image theorem's `Nonempty` conclusion.
   The hypotheses remain arbitrary topological commutative B, one fixed eR and G, hG, any h,
   and any N. The argument uses no points, nonempty objects, nonzero scalars, finiteness, or
   discrete-topology assumption, so empty schemes and the zero ring introduce no extra case.

4. **Route, reuse, and pruning: PASS.** Read `FiniteDiscreteCoefficientEncoding`,
   `FiniteDiscreteRestrictionEncoding`, `ConstantInternalModuleSheafEquivalence`, and the
   coefficient-sections obligation. Searched the library for restriction/forgetful comparisons
   and inspected Mathlib's equivalence normalization API. The existing inverse-image existence
   theorem alone cannot identify this specified direct-image map; reusing its module's explicit
   private direct-image construction avoids repeating the scalar-action proof. Every import is
   used: the original public imports provide the fixed encoding and profinite-instance interface,
   while the new nonpublic import supplies the two private constructions. The old dependency
   `def-weil-pbc-coefficient-derived-functor-api` is accounted for under `No longer needed`;
   no module or import is pruned. Checked `sk-thm-properbasechange.json`'s `realized` statement
   and three step groups: none is removed or bypassed by this normalization below the unit level.

5. **DAG agreement: PASS.** The existing node changes only `proof`, `proof_deps`, and
   `proof_origin`; its statement and Lean record are unchanged. The new dependency list is
   exactly the union of the proof steps' `uses`. The plan explicitly identifies the reused
   private direct-image construction, its coefficient-sections obligation, and the separate
   normalization calculation, matching the Lean rather than claiming that the inverse-image
   existence statement itself determines the normalized direct-image comparison. No new nodes
   require checking or searches.

Second reading changed the report only. No mathematical or Lean repair was needed.

The independent scratch check also compiled the unchanged direct consumer
`Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence` against the newly compiled sandbox
item (14.4 seconds for the item including the axiom queries; 9.3 seconds for the consumer),
without errors or warnings. The required delivery dry run passed compilation and preflight.
