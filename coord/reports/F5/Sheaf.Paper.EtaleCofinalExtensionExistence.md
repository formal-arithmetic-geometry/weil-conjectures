## What changed

The theorem `etaleCofinalExtension_nonempty` is now proved by assembling a transported core extension with its separately normalized level comparison. The proof imports the existing étale cofinal-data module and the two new intermediate modules. The two construction steps are represented by named public statements with their source and proof plans.

## Proved and sorry left

- Proved `AlgebraicGeometry.Etale.SystemProjection.etaleCofinalExtension_nonempty`.
- Split off `etaleCofinalExtension_core_nonempty` in node `lem-pur-etale-cofinal-extension-core`; its proof remains `sorry`.
- Split off `etaleCofinalExtension_level_normalization` in node `lem-pur-etale-cofinal-extension-level-normalization`; its proof remains `sorry`.

The delivered closure therefore closes one upper `sorry` and adds two strictly smaller construction statements.

## No longer needed

None. The existing cofinal-data dependency and the strict-system extension declarations named by the new nodes remain needed by the proof plan.

## Where the brief, the DAG or earlier work was wrong

The original single proof step combined strict-system transport, actual section-site realization, and K-flat level normalization into one obligation. Those are independent construction steps with separate interfaces, so the delivery records them as the two intermediate statements above. The top-level theorem is only the packaging step once those interfaces are available.

## New nodes

- `lem-pur-etale-cofinal-extension-core`
- `lem-pur-etale-cofinal-extension-level-normalization`

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.EtaleCofinalExtensionCore": "7d6a8b8431ecf22e6798aa755e1b42205074f729", "Sheaf.Paper.EtaleCofinalExtensionExistence": "0ff3ed350ef9b374f482ce1749d7d470b3803831", "Sheaf.Paper.EtaleCofinalExtensionLevelNormalization": "cee132ae40d26880a17aa0b1d6db4d5889aa48a7"}, "results": {}, "time": "2026-10-28T04:05:04+0800", "transitive": 0, "version": 1}
```

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
