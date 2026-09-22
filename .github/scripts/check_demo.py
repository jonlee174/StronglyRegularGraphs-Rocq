"""Check the extracted CLI against the expected SRG parameters."""

import subprocess


def check_matrix(kind, size, vertices, degree, lam, mu):
    result = subprocess.run(
        ["./demo", kind, str(size)],
        check=True,
        capture_output=True,
        text=True,
        timeout=60,
    )
    rows = result.stdout.splitlines()
    assert len(rows) == vertices, (kind, size, "vertex count")
    assert all(len(row) == vertices for row in rows), (kind, size, "row length")
    assert all(set(row) <= {"0", "1"} for row in rows), (kind, size, "binary output")
    matrix = [[int(value) for value in row] for row in rows]
    for u in range(vertices):
        assert matrix[u][u] == 0, (kind, size, "loop", u)
        assert sum(matrix[u]) == degree, (kind, size, "degree", u)
        for v in range(u):
            assert matrix[u][v] == matrix[v][u], (kind, size, "symmetry", u, v)
            common = sum(a * b for a, b in zip(matrix[u], matrix[v]))
            expected = lam if matrix[u][v] else mu
            assert common == expected, (kind, size, "common neighbors", u, v)
    print(f"{kind} {size}: SRG({vertices}, {degree}, {lam}, {mu}) OK")


for q in (2, 3, 4):
    check_matrix("hamming", q, q * q, 2 * (q - 1), q - 2, 2)

for p in (5, 13, 17):
    check_matrix("paley", p, p, (p - 1) // 2, (p - 5) // 4, (p - 1) // 4)
