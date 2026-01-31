type CodeMap = Record<string, string>;

const codeFiles = import.meta.glob("/src/assets/code/**/*", {
  eager: true,
  as: "raw",
}) as CodeMap;

const normalizePath = (path: string): string => {
  const trimmed = path.replace(/^[.\/]+/, "");
  if (trimmed.startsWith("src/assets/code/")) {
    return `/${trimmed}`;
  }
  if (trimmed.startsWith("/src/assets/code/")) {
    return trimmed;
  }
  return `/src/assets/code/${trimmed}`;
};

export const getCode = (path: string): string => {
  const normalized = normalizePath(path);
  const code = codeFiles[normalized];
  if (!code) {
    const available = Object.keys(codeFiles)
      .map((key) => key.replace("/src/assets/code/", ""))
      .sort();
    throw new Error(
      `Unknown code snippet "${path}". Available: ${available.join(", ")}`,
    );
  }
  return code;
};

export const getCodeTitle = (path: string): string => {
  const normalized = normalizePath(path);
  return normalized.split("/").pop() ?? normalized;
};
